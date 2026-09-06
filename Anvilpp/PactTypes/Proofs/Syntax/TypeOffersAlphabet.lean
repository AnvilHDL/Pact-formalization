import Anvilpp.PactTypes.Proofs.Syntax.TypeTransitionSystemLemmas

/-!
A decorated step preserves the fixed syntactic alphabet of an
alphabet-well-formed source.  This is the `TypeOffers` counterpart of
`TypeTransition.preserves_alphabet`.
-/

namespace Pact

set_option maxHeartbeats 1000000

theorem TypeOffers.preserves_alphabet
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource : source.AlphabetWellFormed)
    (hOffers : TypeOffers env source label target current future) :
    target.alphabet = source.alphabet := by
  induction hOffers with
  | action => simp [PactType.alphabet]
  | action_wait => simp [PactType.alphabet]
  | choice_left =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | choice_right =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | fair_left =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | fair_right =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | cycle => simp [PactType.alphabet]
  | cycle_wait => simp [PactType.alphabet]
  | skip => simp [PactType.alphabet]
  | progress => simp [PactType.alphabet]
  | recur env alphabet name body =>
      simp only [PactType.AlphabetWellFormed] at hSource
      have hBody : body.alphabet = alphabet := hSource.2.1
      have hReplacement :
          (PactType.recur alphabet name body).alphabet = body.alphabet := by
        simpa [PactType.alphabet] using hBody.symm
      have hReplace :=
        PactType.replaceVar_alphabet_eq_of_replacement body name hReplacement
      change (body.replaceVar name (PactType.recur alphabet name body)).alphabet =
        alphabet
      exact hReplace.trans hBody
  | seq => simp [PactType.alphabet]
  | seq_tock => simp [PactType.alphabet]
  | seq_fuse =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | seq_fuse_tock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | xoffer_branch env alphabet elseType branches action processType conditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      have hBranch : processType.alphabet = alphabet :=
        PactType.branch_alphabet_eq_of_mem hSource.2.2.2 conditions.2.1
      simpa [PactType.alphabet] using hBranch
  | xoffer_else =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | xoffer_wait => simp [PactType.alphabet]
  | offer_some env alphabet elseType branches enabled conditions =>
      have hSelected :
          (parallelTypeBranchesSelecting alphabet enabled branches).alphabet =
            alphabet :=
        parallelTypeBranchesSelecting_alphabet_eq_of_mem conditions.2.1
      simpa [PactType.alphabet] using hSelected
  | offer_else =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | offer_wait => simp [PactType.alphabet]
  | par => simp [PactType.alphabet]
  | par_fuse => simp [PactType.alphabet]
  | par_fuse_tock => simp [PactType.alphabet]
  | left_complete =>
      rw [PactType.reannotate_alphabet]
      simp [PactType.alphabet]
  | right_complete =>
      rw [PactType.reannotate_alphabet]
      simp [PactType.alphabet]

end Pact
