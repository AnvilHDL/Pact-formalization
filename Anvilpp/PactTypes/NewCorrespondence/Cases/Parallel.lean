import Anvilpp.PactTypes.NewCorrespondence.Cases.Base

namespace Pact

open Classical
open Pact.NewCorrespondence

noncomputable section
set_option maxHeartbeats 40000000 in
/-- Step correspondence for interleaved parallel composition `τ1 ‖_I τ2`. -/
theorem correspondence_par_stepIff
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hParentAlphabet : alphabet =
      PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface)
    (hParallelCompatible : PactTypeAlphabet.ParallelCompatible alphabet
      left.alphabet right.alphabet left right interface)
    -- `ParallelMessageOwnership`'s action clause for this node.
    (hMessageDisjoint :
      Disjoint (PactType.MessageActions left) (PactType.MessageActions right))
    (hLeftResidual : left.ResidualInvariant)
    (hRightResidual : right.ResidualInvariant)
    (hAlphabetCoherent :
      (.par alphabet left right interface : PactType).AlphabetCoherent)
    (hLeftIH : StepIffStatement left)
    (hRightIH : StepIffStatement right) :
    StepIffStatement (.par alphabet left right interface) := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

end

end Pact
