import Anvilpp.ProofHelpers.Inference.ConjunctPreservation
import Anvilpp.ProofHelpers.Process
import Anvilpp.ProofHelpers.Regularity
import Anvilpp.PactTypes.Proofs.Correspondence.CasesTop
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.SurvivorTransport
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.AlphabetPreservation

/-!
# Represented residuals

The paper's appeal in "Decorated steps lift": one-step abstraction along the
reaching execution gives a type execution from `abs(P_*)` to `abs(P)`, and by
Lemma 4.5 every residual of that execution is represented by a compiled state,
so it keeps the alphabet discipline.
-/

namespace Pact

noncomputable section

open Classical

/-- The admissibility premise of Lemma 4.5, read off `TypeWF_∅`. -/
theorem admissibleType_of_typeWellFormedIn_nil {processType : PactType}
    (hWF : TypeWellFormedIn [] processType) : AdmissibleType processType := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO, hMenu⟩ := hWF
  exact ⟨hA, hPL, hFL, hB, hH, hCG, hTR, hSC, hMO, hIS, hIAS, hCMO, hMenu⟩

/-- A residual represented by a compiled state keeps the alphabet discipline. -/
theorem represented_alphabetWellFormed {source residual : PactType}
    {state : TypeAutomatonState} (hWF : TypeWellFormedIn [] source)
    (hRelated : relationMembership (buildRelationSet source (compileType source))
      residual state) : residual.AlphabetWellFormed := by
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hWF
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO, hMenu⟩ := hWF
  exact relationMembership_alphabetWellFormed committedOfferAlphabetWellFormed_holds
    committedOfferScoping_holds source residual state hA hIS hIAS hTR hDisjoint
    hRelated

/-- A type step from a represented residual lands on a represented residual. -/
theorem represented_step {source residual target : PactType}
    {state : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    (hAdmissible : AdmissibleType source)
    (hRelated : relationMembership (buildRelationSet source (compileType source))
      residual state)
    (hStep : TypeTransition env residual label target) :
    ∃ state', relationMembership (buildRelationSet source (compileType source))
      target state' := by
  obtain ⟨current, future, hOffers⟩ := hStep.exists_typeOffers
  obtain ⟨state', -, hRelated'⟩ :=
    (correspondence_steps source hAdmissible).1 (offers := ⟨current, future⟩)
      hRelated ⟨hStep, hOffers⟩
  exact ⟨state', hRelated'⟩

/-! ## Along a process execution -/

/-- Every reachable residual of a well-formed process has a represented
abstraction and keeps its conjunctive heads distinct. -/
theorem prefixValid_represented {initial : Proc}
    (hWF : TypeWellFormedIn [] (inferProcess initial))
    (hConj : Proc.ConjunctRegular initial) :
    ∀ {entries : List (Environment × Label × Proc)} {residual : Proc},
      PrefixValid initial entries residual →
      (∃ state, relationMembership
          (buildRelationSet (inferProcess initial)
            (compileType (inferProcess initial)))
          (inferProcess residual) state) ∧ Proc.ConjunctRegular residual := by
  intro entries residual hValid
  induction hValid with
  | root =>
      exact ⟨⟨(compileType (inferProcess initial)).initial,
        buildRelationSet_initial _ _⟩, hConj⟩
  | step hPrefix hStep ih =>
      obtain ⟨⟨state, hRelated⟩, hConjCurrent⟩ := ih
      have hAlphaCurrent : Proc.AlphabetWellFormed _ :=
        (Proc.alphabetWellFormed_iff _).2
          (represented_alphabetWellFormed hWF hRelated)
      obtain ⟨current, future, hOffers⟩ := hStep
      refine ⟨represented_step (admissibleType_of_typeWellFormedIn_nil hWF)
          hRelated (one_step_abstraction hAlphaCurrent hConjCurrent
            ⟨current, future, hOffers⟩),
        conjunctRegular_offers hOffers hConjCurrent⟩

/-- `AlphaWF_P` and distinct conjunctive heads at every reachable residual. -/
theorem prefixValid_sideConditions {initial : Proc}
    (hWF : TypeWellFormedIn [] (inferProcess initial))
    (hConj : Proc.ConjunctRegular initial)
    {entries : List (Environment × Label × Proc)} {residual : Proc}
    (hValid : PrefixValid initial entries residual) :
    Proc.AlphabetWellFormed residual ∧ Proc.ConjunctRegular residual := by
  obtain ⟨⟨state, hRelated⟩, hConjResidual⟩ :=
    prefixValid_represented hWF hConj hValid
  exact ⟨(Proc.alphabetWellFormed_iff residual).2
    (represented_alphabetWellFormed hWF hRelated), hConjResidual⟩

end

end Pact
