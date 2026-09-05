import Anvilpp.PactTypes.Syntax.TypeTransitionSystemDefs

namespace Pact

noncomputable section

/-- Every semantic type step carries at least one environment-specific offer pair. -/
theorem TypeTransition.exists_typeOffers
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (transition : TypeTransition env source label target) :
    ∃ current future, TypeOffers env source label target current future := by
  induction transition with
  | action env alphabet msg dir conditions hAlphabet =>
      exact ⟨{(msg, dir)}, typeFutureOffers (.skip alphabet),
        TypeOffers.action env alphabet msg dir conditions hAlphabet⟩
  | action_wait env alphabet msg dir conditions hAlphabet =>
      exact ⟨{(msg, dir)},
        typeFutureOffers (.message alphabet msg dir) \ {(msg, dir)},
        TypeOffers.action_wait env alphabet msg dir conditions hAlphabet⟩
  | choice_left env alphabet left right hEnv hClock =>
      exact ⟨∅, typeFutureOffers left,
        TypeOffers.choice_left env alphabet left right ⟨hEnv, hClock⟩⟩
  | choice_right env alphabet left right hEnv hClock =>
      exact ⟨∅, typeFutureOffers right,
        TypeOffers.choice_right env alphabet left right ⟨hEnv, hClock⟩⟩
  | fair_left env alphabet bid left right hEnv hClock =>
      exact ⟨∅, typeFutureOffers left,
        TypeOffers.fair_left env alphabet bid left right ⟨hEnv, hClock⟩⟩
  | fair_right env alphabet bid left right hEnv hClock =>
      exact ⟨∅, typeFutureOffers right,
        TypeOffers.fair_right env alphabet bid left right ⟨hEnv, hClock⟩⟩
  | cycle env alphabet conditions =>
      exact ⟨∅, ∅, TypeOffers.cycle env alphabet conditions⟩
  | cycle_wait env alphabet conditions =>
      exact ⟨∅, ∅, TypeOffers.cycle_wait env alphabet conditions⟩
  | skip env alphabet conditions =>
      exact ⟨∅, ∅, TypeOffers.skip env alphabet conditions⟩
  | seq_fuse env alphabet skipAlphabet left right label _ ihLeft =>
      obtain ⟨current, childFuture, hOffers⟩ := ihLeft
      by_cases hTock : label = TypeLabel.tock
      · subst hTock
        exact ⟨∅, ∅,
          TypeOffers.seq_fuse_tock env alphabet skipAlphabet left right current
            childFuture hOffers⟩
      · exact ⟨current, typeFutureOffers right \ current,
          TypeOffers.seq_fuse env alphabet skipAlphabet left right label current
            childFuture hOffers hTock⟩
  | progress env alphabet pid hEnv hClock =>
      exact ⟨∅, ∅, TypeOffers.progress env alphabet pid ⟨hEnv, hClock⟩⟩
  | recur env alphabet name body hEnv hClock =>
      exact ⟨∅,
        typeFutureOffers (body.replaceVar name (.recur alphabet name body)),
        TypeOffers.recur env alphabet name body ⟨hEnv, hClock⟩⟩
  | seq env alphabet left left' right label _ hNotSkip ihLeft =>
      obtain ⟨current, childFuture, hOffers⟩ := ihLeft
      by_cases hTock : label = TypeLabel.tock
      · subst hTock
        exact ⟨∅, ∅,
          TypeOffers.seq_tock env alphabet left left' right current childFuture
            hOffers hNotSkip⟩
      · exact ⟨current, typeFutureOffers (.seq alphabet left' right) \ current,
          TypeOffers.seq env alphabet left left' right label current childFuture
            hOffers hNotSkip hTock⟩
  | xoffer_branch env alphabet elseType branches action processType conditions
      hAlphabet =>
      exact ⟨{action}, typeFutureOffers processType \ {action},
        TypeOffers.xoffer_branch env alphabet elseType branches action
          processType conditions hAlphabet⟩
  | xoffer_else env alphabet elseType branches conditions hAlphabet =>
      exact ⟨∅, typeFutureOffers elseType,
        TypeOffers.xoffer_else env alphabet elseType branches conditions
          hAlphabet⟩
  | xoffer_wait env alphabet elseType branches conditions hAlphabet =>
      exact ⟨typeWaitingOffers env branches,
        typeFutureOffers (.xoffer alphabet elseType branches) \
          typeWaitingOffers env branches,
        TypeOffers.xoffer_wait env alphabet elseType branches conditions
          hAlphabet⟩
  | offer_some env alphabet elseType branches enabled conditions hAlphabet =>
      exact ⟨∅,
        typeFutureOffers
          (parallelTypeBranchesSelecting alphabet enabled branches),
        TypeOffers.offer_some env alphabet elseType branches enabled conditions
          hAlphabet⟩
  | offer_else env alphabet elseType branches conditions hAlphabet =>
      exact ⟨typeBranchActions branches,
        typeFutureOffers elseType \ typeBranchActions branches,
        TypeOffers.offer_else env alphabet elseType branches conditions
          hAlphabet⟩
  | offer_wait env alphabet elseType branches conditions hAlphabet =>
      exact ⟨typeBranchActions branches,
        typeFutureOffers (.offer alphabet elseType branches) \
          typeBranchActions branches,
        TypeOffers.offer_wait env alphabet elseType branches conditions
          hAlphabet⟩
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftNotSkip
      hRightNotSkip _ hLeftOffers
      _ hRightOffers hNotBothSkip conditions ihLeft ihRight =>
      exact ⟨hideTypeOffers interface (leftCurrent ∪ rightCurrent),
        (if TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock
          then ∅
          else typeFutureOffers (.par alphabet left' right' interface) \
            hideTypeOffers interface (leftCurrent ∪ rightCurrent)),
        TypeOffers.par outer leftEnv rightEnv interface alphabet left left' right right'
          leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
          hLeftNotSkip hRightNotSkip
          hLeftOffers hRightOffers hNotBothSkip conditions.2.1
          conditions.2.2.1 ⟨conditions.1, conditions.2.2.2⟩⟩
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture _ hLeftOffers _
      hRightOffers conditions ihLeft ihRight =>
      by_cases hTock :
          TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock
      · exact ⟨∅, ∅,
          TypeOffers.par_fuse_tock outer leftEnv rightEnv interface alphabet left right
            leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
            hLeftOffers hRightOffers conditions.2.1 conditions.2.2.1
            ⟨conditions.1, conditions.2.2.2⟩ hTock⟩
      · exact ⟨hideTypeOffers interface (leftCurrent ∪ rightCurrent),
          hideTypeOffers interface (leftFuture ∪ rightFuture),
          TypeOffers.par_fuse outer leftEnv rightEnv interface alphabet left right
            leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
            hLeftOffers hRightOffers conditions.2.1 conditions.2.2.1
            ⟨conditions.1, conditions.2.2.2⟩ hTock⟩
  | left_complete outer rightEnv interface alphabet left right right' rightLabel
      rightCurrent rightFuture hLeftSkip hRightNotSkip _ hRightOffers hNotSkip
      hRightCurrentHidden hRightFutureHidden hLocal hWF ihRight =>
      by_cases hTock : rightLabel = TypeLabel.tock
      · exact ⟨∅, ∅,
          TypeOffers.left_complete_tock outer rightEnv interface alphabet left right
            right' rightLabel rightCurrent rightFuture hLeftSkip hRightNotSkip
            hRightOffers hNotSkip
            hRightCurrentHidden hRightFutureHidden hLocal hWF hTock⟩
      · exact ⟨hideTypeOffers interface rightCurrent,
          typeFutureOffers (right'.reannotate alphabet) \
            hideTypeOffers interface rightCurrent,
          TypeOffers.left_complete outer rightEnv interface alphabet left right right'
            rightLabel rightCurrent rightFuture hLeftSkip hRightNotSkip
            hRightOffers hNotSkip
            hRightCurrentHidden hRightFutureHidden hLocal hWF hTock⟩
  | right_complete outer leftEnv interface alphabet left left' right leftLabel
      leftCurrent leftFuture hRightSkip hLeftNotSkip _ hLeftOffers hNotSkip
      hLeftCurrentHidden hLeftFutureHidden hLocal hWF ihLeft =>
      by_cases hTock : leftLabel = TypeLabel.tock
      · exact ⟨∅, ∅,
          TypeOffers.right_complete_tock outer leftEnv interface alphabet left left'
            right leftLabel leftCurrent leftFuture hRightSkip hLeftNotSkip
            hLeftOffers hNotSkip
            hLeftCurrentHidden hLeftFutureHidden hLocal hWF hTock⟩
      · exact ⟨hideTypeOffers interface leftCurrent,
          typeFutureOffers (left'.reannotate alphabet) \
            hideTypeOffers interface leftCurrent,
          TypeOffers.right_complete outer leftEnv interface alphabet left left' right
            leftLabel leftCurrent leftFuture hRightSkip hLeftNotSkip
            hLeftOffers hNotSkip
            hLeftCurrentHidden hLeftFutureHidden hLocal hWF hTock⟩

/-- Package a semantic step together with one of its offer pairs. -/
theorem TypeTransition.exists_decorated
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (transition : TypeTransition env source label target) :
    ∃ offers, DecoratedTypeTransition env source label offers target := by
  obtain ⟨current, future, hOffers⟩ := transition.exists_typeOffers
  exact ⟨{ current := current, future := future }, transition, hOffers⟩

/-- A semantic type step preserves the fixed syntactic alphabet of an
admissible source type.  The transition rules are intentionally not cluttered
with these equalities; they are recovered from `AlphabetWellFormed`. -/
theorem TypeTransition.preserves_alphabet
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (hSource : source.AlphabetWellFormed)
    (transition : TypeTransition env source label target) :
    target.alphabet = source.alphabet := by
  induction transition with
  | action env alphabet msg dir conditions =>
      simp [PactType.alphabet]
  | action_wait env alphabet msg dir conditions =>
      simp [PactType.alphabet]
  | choice_left env alphabet left right hEnv hClock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | choice_right env alphabet left right hEnv hClock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | fair_left env alphabet bid left right hEnv hClock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | fair_right env alphabet bid left right hEnv hClock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | cycle env alphabet conditions =>
      simp [PactType.alphabet]
  | cycle_wait env alphabet conditions =>
      simp [PactType.alphabet]
  | skip env alphabet conditions =>
      simp [PactType.alphabet]
  | seq_fuse env alphabet skipAlphabet left right label childTransition ihLeft =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | progress env alphabet pid hEnv hClock =>
      simp [PactType.alphabet]
  | recur env alphabet name body hEnv hClock =>
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
  | seq env alphabet left left' right label childTransition hNotSkip ihLeft =>
      simp [PactType.alphabet]
  | xoffer_branch env alphabet elseType branches action processType conditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      have hBranch :
          processType.alphabet = alphabet :=
        PactType.branch_alphabet_eq_of_mem hSource.2.2.2 conditions.2.1
      simpa [PactType.alphabet] using hBranch
  | xoffer_else env alphabet elseType branches conditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | xoffer_wait env alphabet elseType branches conditions =>
      simp [PactType.alphabet]
  | offer_some env alphabet elseType branches enabled conditions =>
      have hSelected :
          (parallelTypeBranchesSelecting alphabet enabled branches).alphabet =
            alphabet :=
        parallelTypeBranchesSelecting_alphabet_eq_of_mem conditions.2.1
      simpa [PactType.alphabet] using hSelected
  | offer_else env alphabet elseType branches conditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | offer_wait env alphabet elseType branches conditions =>
      simp [PactType.alphabet]
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture leftTransition
      hLeftOffers rightTransition hRightOffers hNotBothSkip conditions ihLeft
      ihRight =>
      simp [PactType.alphabet]
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture leftTransition
      hLeftOffers rightTransition hRightOffers conditions ihLeft ihRight =>
      simp [PactType.alphabet]
  | left_complete outer rightEnv interface alphabet left right right' rightLabel
      rightCurrent rightFuture hLeftSkip hRightNotSkip rightTransition
      hRightOffers hNotSkip _ _ hLocal hWF ihRight =>
      rw [PactType.reannotate_alphabet]
      simp [PactType.alphabet]
  | right_complete outer leftEnv interface alphabet left left' right leftLabel
      leftCurrent leftFuture hRightSkip hLeftNotSkip leftTransition
      hLeftOffers hNotSkip _ _ hLocal hWF ihLeft =>
      rw [PactType.reannotate_alphabet]
      simp [PactType.alphabet]

end

end Pact
