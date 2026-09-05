import Anvilpp.PactTypes.Syntax.PactTypeSubstitutionLemmas
import Anvilpp.PactTypes.NewCorrespondence.Helpers.AlphabetPreservation
import Anvilpp.PactTypes.Syntax.PactTypeFutureOffersDefs
import Anvilpp.PactTypes.Automata.SyncEdgesDefs
import Anvilpp.PactTypes.Syntax.PactTypeRegularityLemmas
import Anvilpp.PactTypes.Syntax.TypeTransitionSystemDefs
import Anvilpp.PactTypes.Syntax.LiveEquivalenceLemmas
import Anvilpp.PactTypes.Syntax.TypeOffersAlphabet
import Anvilpp.PactTypes.Syntax.TypeTransitionSystemLemmas
import Anvilpp.PactTypes.NewCorrespondence.Helpers.MainHelpers

/-!
Live-equivalent residuals take the same decorated steps.
-/

namespace Pact

namespace PactType

/-! ### Transporting a parallel child's local environment -/

/-! ### The offer side conditions read branch heads only, so they transport -/

/-! ### The syntactic future menu stays inside the source's own actions -/

/-- A step is offered only to an environment well formed for its source. -/
theorem typeOffers_env_wellFormed :
    ∀ {env : TypeEnvironment} {rho : PactType} {label : TypeLabel}
      {rho' : PactType} {current future : Finset BareMessage},
      TypeOffers env rho label rho' current future →
      rho.AlphabetWellFormed → env.WellFormed rho.alphabet := by
  intro env rho label rho' current future hOffers
  induction hOffers with
  | seq _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro hWF
      simp only [PactType.AlphabetWellFormed] at hWF
      have h := ih hWF.2.2.2.1
      rw [hWF.2.1] at h
      exact h
  | seq_tock _ _ _ _ _ _ _ _ _ ih =>
      intro hWF
      simp only [PactType.AlphabetWellFormed] at hWF
      have h := ih hWF.2.2.2.1
      rw [hWF.2.1] at h
      exact h
  | seq_fuse _ _ _ _ _ _ _ _ _ _ ih =>
      intro hWF
      simp only [PactType.AlphabetWellFormed] at hWF
      have h := ih hWF.2.2.2.1
      rw [hWF.2.1] at h
      exact h
  | seq_fuse_tock _ _ _ _ _ _ _ _ ih =>
      intro hWF
      simp only [PactType.AlphabetWellFormed] at hWF
      have h := ih hWF.2.2.2.1
      rw [hWF.2.1] at h
      exact h
  | _ =>
      intro _
      simp only [PactType.alphabet]
      tauto

end PactType

end Pact
