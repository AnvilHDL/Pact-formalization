import Anvilpp.PactTypes.NewCorrespondence.Cases.Base

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Forward bridge needed by the recursion case.

If a substituted body residual takes a semantic step, the compiled recursion
must have the matching edge from the tagged body state.  This is the precise
replacement for the old unrestricted substitution lemma in the forward body
case. -/
def RecursionBodyForwardObligation
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType) : Prop :=
  ∀ {bodyResidual target : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    relationMembership (buildRelationSet body (compileType signature body))
      bodyResidual state →
    TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.recur alphabet name body)).alphabet →
    DecoratedTypeTransition env
      (bodyResidual.replaceVar name (.recur alphabet name body))
      label offers target →
    ∃ targetState,
      (compileType signature (.recur alphabet name body)).HasEdge
        (.child 0 state) env label offers targetState ∧
      relationMembership
        (buildRelationSet (.recur alphabet name body)
          (compileType signature (.recur alphabet name body)))
        target targetState

/-- Backward bridge needed by the recursion case.

If the compiled recursion has an edge from a tagged body state, then the
substituted body residual has the matching semantic step.  This obligation
contains the copied-edge and marker/backedge subcases. -/
def RecursionBodyBackwardObligation
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType) : Prop :=
  ∀ {bodyResidual target : PactType} {state targetState : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    relationMembership (buildRelationSet body (compileType signature body))
      bodyResidual state →
    TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.recur alphabet name body)).alphabet →
    (compileType signature (.recur alphabet name body)).HasEdge
      (.child 0 state) env label offers targetState →
    relationMembership
      (buildRelationSet (.recur alphabet name body)
        (compileType signature (.recur alphabet name body)))
      target targetState →
    DecoratedTypeTransition env
      (bodyResidual.replaceVar name (.recur alphabet name body))
      label offers target

/-- Forward body bridge for the recursion case.

This is the caller-side obligation for the body case of `μX.body`.
It is intentionally separate from `correspondence_recur_stepIff`: the proof
uses the handwritten recursion premises, especially tail position of `X`,
to distinguish copied non-marker body edges from installed backedges. -/
theorem recursion_body_forward_obligation
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (_hBodyAlphabet : body.alphabet = alphabet)
    (_hBodyTail : body.TailOccurrences name True)
    (_hAdmissible : AdmissibleType signature (.recur alphabet name body))
    (_hBodyIH : StepIffStatement signature body) :
    RecursionBodyForwardObligation signature alphabet name body := by
  sorry -- TODO(section7): copied-body/marker split under tail-recursive recursion.

/-- Backward body bridge for the recursion case.

This is the reverse direction of `recursion_body_forward_obligation`: every
public edge from a tagged body state is either a copied body edge or the
installed backedge for the bound marker. -/
theorem recursion_body_backward_obligation
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (_hBodyAlphabet : body.alphabet = alphabet)
    (_hBodyTail : body.TailOccurrences name True)
    (_hAdmissible : AdmissibleType signature (.recur alphabet name body))
    (_hBodyIH : StepIffStatement signature body) :
    RecursionBodyBackwardObligation signature alphabet name body := by
  sorry -- TODO(section7): copied-body/marker split under tail-recursive recursion.

/-- Step correspondence for recursion `μX.body`. -/
theorem correspondence_recur_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (_hBodyAlphabet : body.alphabet = alphabet)
    (_hBodyTail : body.TailOccurrences name True)
    (_hAdmissible : AdmissibleType signature (.recur alphabet name body))
    (_hBodyIH : StepIffStatement signature body)
    (hBodyForward : RecursionBodyForwardObligation signature alphabet name body)
    (hBodyBackward : RecursionBodyBackwardObligation signature alphabet name body) :
    StepIffStatement signature (.recur alphabet name body) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's unfolding step matches the
  -- header edge, and `hBodyIH` transported along substitution handles the
  -- rest of the body, including a marker turning into a backedge.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabetFor alphabet := by
    simpa [compileType] using hSymbol
  have hFuelEq : typeCompilationFuel (.recur alphabet name body) = typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body) =
        buildRecursionAutomaton signature name
          (compileTypeFuel signature (typeCompilationFuel body) body) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
  rcases relationMembership_recur_cases signature alphabet name body hRelated with
    hRoot | ⟨q, bodyResidual, hEntryEq, hBodyRelated⟩
  · -- root case: `residual` represents `μX.body` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabetFor_environment_mem signature alphabet hSignatureSymbol
    have hHeaderPending :
        ({ source := TypeAutomatonState.root, environment := env,
            label := AutomatonConstructionLabel.visible TypeLabel.silent,
            current := (∅ : Finset BareMessage),
            future := FutureSpec.at (childState 0
              (compileTypeFuel signature (typeCompilationFuel body) body).initial) ∅,
            target := childState 0
              (compileTypeFuel signature (typeCompilationFuel body) body).initial } :
          PendingAutomatonEdge) ∈
          (buildRecursionAutomaton signature name
            (compileTypeFuel signature (typeCompilationFuel body) body)).edges := by
      simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image]
      exact Or.inl ⟨env, hEnvMem, rfl⟩
    have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
    have hRecurStep : DecoratedTypeTransition env (.recur alphabet name body) TypeLabel.silent
        (TypeOfferSummary.mk ∅ (typeFutureOffers (body.replaceVar name (.recur alphabet name body))))
        (body.replaceVar name (.recur alphabet name body)) :=
      ⟨TypeTransition.recur env alphabet name body hWF, TypeOffers.recur env alphabet name body hWF⟩
    constructor
    · intro hStep
      obtain ⟨hTrans, hOffers⟩ := hStep
      generalize hLabelEq : label = actualLabel at hTrans
      generalize hTargetEq : residual' = actualTarget at hTrans
      cases hTrans
      rw [hLabelEq, hTargetEq] at hOffers
      generalize hCurrentEq : current = actualCurrent at hOffers
      generalize hFutureEq : future = actualFuture at hOffers
      cases hOffers
      have hSignatureSymbol' :
          TypeAutomatonSymbol.mk env TypeLabel.silent
              (TypeOfferSummary.mk ∅
                (typeFutureOffers (body.replaceVar name (.recur alphabet name body)))) ∈
            (compileType signature (.recur alphabet name body)).alphabet := by
        rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
        exact hSignatureSymbol
      have hEdgeFact :
          (compileType signature (.recur alphabet name body)).HasEdge TypeAutomatonState.root
            env TypeLabel.silent
            (TypeOfferSummary.mk ∅
              (typeFutureOffers (body.replaceVar name (.recur alphabet name body))))
            (.child 0 (compileTypeFuel signature (typeCompilationFuel body)
              body).initial) := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.recur alphabet name body)
          TypeAutomatonState.root (.child 0 (compileTypeFuel signature
            (typeCompilationFuel body) body).initial) env TypeLabel.silent
          (TypeOfferSummary.mk ∅
            (typeFutureOffers (body.replaceVar name (.recur alphabet name body))))
          hSignatureSymbol']
        rw [hWhole]
        refine ⟨_, hHeaderPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
        simp only [childState, Finset.sdiff_empty]
        exact helper_h15_recursion_future_offers_agree signature alphabet name body
          (buildRelationSet_initial body (compileType signature body))
      refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel body)
        body).initial, hEdgeFact, ?_⟩
      exact relationMembership_recur_child signature alphabet name body body
        (buildRelationSet_initial body (compileType signature body))
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hSymbolMem := compileType_hasEdge_symbol_mem signature (.recur alphabet name body)
        hEdge
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.recur alphabet name body) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future) hSymbolMem).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image] at hPendingMem
      rcases hPendingMem with ⟨environment, hEnvironment, hEq⟩ | ⟨bodyEdge, _, hEq⟩
      · subst hEq
        simp only [childState] at hPLabel hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hTargetEq : state' = .child 0
            (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
          rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        rcases relationMembership_recur_cases signature alphabet name body hTargetRelated with
          hRootAgain | ⟨qAgain, bodyResidualAgain, hEntryEqAgain, hBodyRelatedAgain⟩
        · exact absurd (congrArg Prod.snd hRootAgain)
            (by simp)
        · simp only [Prod.mk.injEq] at hEntryEqAgain
          obtain ⟨hResidualEqAgain, hStateEqAgain⟩ := hEntryEqAgain
          have hQAgainEq : qAgain =
              (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
            simpa [childState] using hStateEqAgain.symm
          rw [hQAgainEq] at hBodyRelatedAgain
          have hBodyEq : bodyResidualAgain = body :=
            relationMembership_functional body (compileType signature body)
              hBodyRelatedAgain (buildRelationSet_initial body (compileType signature body))
          rw [hBodyEq] at hResidualEqAgain
          have hPFuture' : computeFutureOf signature (.recur alphabet name body)
              (childState 0 (compileTypeFuel signature (typeCompilationFuel body)
                body).initial) \ (∅ : Finset BareMessage) = future := hPFuture
          have hFutureEq : future =
              typeFutureOffers (body.replaceVar name (.recur alphabet name body)) := by
            rw [← hPFuture', Finset.sdiff_empty, childState]
            exact helper_h15_recursion_future_offers_agree signature alphabet name body
              (buildRelationSet_initial body (compileType signature body))
          have hEnvironmentEq : environment = env := hPEnv
          rw [hResidualEqAgain, hLabelEq]
          refine ⟨TypeTransition.recur env alphabet name body
            (localEnvironment_wellFormed signature (hEnvironmentEq ▸ hEnvironment)), ?_⟩
          rw [hCurrentEq, hFutureEq]
          exact TypeOffers.recur env alphabet name body
            (localEnvironment_wellFormed signature (hEnvironmentEq ▸ hEnvironment))
      · exfalso
        have hRootSource : pendingEdge.source = TypeAutomatonState.root := hPSource
        rw [← hEq] at hRootSource
        split at hRootSource <;> simp [childState] at hRootSource
  · -- body case: `residual` represents `bodyResidual` substituted for the open variable
    simp only [Prod.mk.injEq] at hEntryEq
    obtain ⟨hResidualEq, hStateEq⟩ := hEntryEq
    subst hResidualEq; subst hStateEq
    constructor
    · intro hStep
      have hWitness := hBodyForward hBodyRelated hSymbol hStep
      exact hWitness
    · rintro ⟨state', hEdge, hTargetRelated⟩
      exact hBodyBackward hBodyRelated hSymbol hEdge hTargetRelated



end

end Pact
