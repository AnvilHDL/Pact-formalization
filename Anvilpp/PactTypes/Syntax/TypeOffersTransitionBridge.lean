import Anvilpp.PactTypes.Syntax.TypeTransitionSystemDefs

/-!
Every offers derivation carries the underlying transition of the same step.
-/

namespace Pact

theorem TypeOffers.toTransition {env : TypeEnvironment} {source : PactType}
    {label : TypeLabel} {target : PactType} {current future : Finset BareMessage}
    (h : TypeOffers env source label target current future) :
    TypeTransition env source label target := by
  induction h with
  | action env alphabet msg dir hEnv hMem => exact .action env alphabet msg dir hEnv hMem
  | action_wait env alphabet msg dir hEnv hMem =>
      exact .action_wait env alphabet msg dir hEnv hMem
  | choice_left env alphabet left right hEnv => exact .choice_left env alphabet left right hEnv.1 hEnv.2
  | choice_right env alphabet left right hEnv => exact .choice_right env alphabet left right hEnv.1 hEnv.2
  | fair_left env alphabet bid left right hEnv =>
      exact .fair_left env alphabet bid left right hEnv.1 hEnv.2
  | fair_right env alphabet bid left right hEnv =>
      exact .fair_right env alphabet bid left right hEnv.1 hEnv.2
  | cycle env alphabet hEnv => exact .cycle env alphabet hEnv
  | cycle_wait env alphabet hEnv => exact .cycle_wait env alphabet hEnv
  | skip env alphabet hEnv => exact .skip env alphabet hEnv
  | progress env alphabet pid hEnv => exact .progress env alphabet pid hEnv.1 hEnv.2
  | recur env alphabet name body hEnv => exact .recur env alphabet name body hEnv.1 hEnv.2
  | seq env alphabet left left' right label current childFuture _ hNotSkip _ ih =>
      exact .seq env alphabet left left' right label ih hNotSkip
  | seq_tock env alphabet left left' right current childFuture _ hNotSkip ih =>
      exact .seq env alphabet left left' right TypeLabel.tock ih hNotSkip
  | seq_fuse env alphabet skipAlphabet left right label current childFuture _ _ ih =>
      exact .seq_fuse env alphabet skipAlphabet left right label ih
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture _ ih =>
      exact .seq_fuse env alphabet skipAlphabet left right TypeLabel.tock ih
  | xoffer_branch env alphabet elseType branches action processType hEnv hDecl =>
      exact .xoffer_branch env alphabet elseType branches action processType hEnv hDecl
  | xoffer_else env alphabet elseType branches hEnv hDecl =>
      exact .xoffer_else env alphabet elseType branches hEnv hDecl
  | xoffer_wait env alphabet elseType branches hEnv hDecl =>
      exact .xoffer_wait env alphabet elseType branches hEnv hDecl
  | offer_some env alphabet elseType branches enabled hEnv hDecl =>
      exact .offer_some env alphabet elseType branches enabled hEnv hDecl
  | offer_else env alphabet elseType branches hEnv hDecl =>
      exact .offer_else env alphabet elseType branches hEnv hDecl
  | offer_wait env alphabet elseType branches hEnv hDecl =>
      exact .offer_wait env alphabet elseType branches hEnv hDecl
  | par outer leftEnv rightEnv interface left left' right right' leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftLive hRightLive hLeftOffers
      hRightOffers hNotBothSkip hLocalLeft hLocalRight hSync ihLeft ihRight =>
      exact .par outer leftEnv rightEnv interface left left' right right' leftLabel
        rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftLive hRightLive
        ihLeft hLeftOffers ihRight hRightOffers hNotBothSkip
        ⟨hSync.1, hLocalLeft, hLocalRight, hSync.2⟩
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocalLeft hLocalRight hSync _ ihLeft ihRight =>
      exact .par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
        leftCurrent leftFuture rightCurrent rightFuture ihLeft hLeftOffers ihRight
        hRightOffers ⟨hSync.1, hLocalLeft, hLocalRight, hSync.2⟩
  | par_fuse_tock outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocalLeft hLocalRight hSync _ ihLeft ihRight =>
      exact .par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
        leftCurrent leftFuture rightCurrent rightFuture ihLeft hLeftOffers ihRight
        hRightOffers ⟨hSync.1, hLocalLeft, hLocalRight, hSync.2⟩
  | left_complete outer rightEnv interface left right right' rightLabel rightCurrent
      rightFuture hLeftSkip hRightLive hRightOffers hTargetLive hCurrent hFuture
      hLocal hWellFormed _ ih =>
      exact .left_complete outer rightEnv interface left right right' rightLabel
        rightCurrent rightFuture hLeftSkip hRightLive ih hRightOffers hTargetLive
        hCurrent hFuture hLocal hWellFormed
  | left_complete_tock outer rightEnv interface left right right' rightLabel rightCurrent
      rightFuture hLeftSkip hRightLive hRightOffers hTargetLive hCurrent hFuture
      hLocal hWellFormed _ ih =>
      exact .left_complete outer rightEnv interface left right right' rightLabel
        rightCurrent rightFuture hLeftSkip hRightLive ih hRightOffers hTargetLive
        hCurrent hFuture hLocal hWellFormed
  | right_complete outer leftEnv interface left left' right leftLabel leftCurrent
      leftFuture hRightSkip hLeftLive hLeftOffers hTargetLive hCurrent hFuture
      hLocal hWellFormed _ ih =>
      exact .right_complete outer leftEnv interface left left' right leftLabel
        leftCurrent leftFuture hRightSkip hLeftLive ih hLeftOffers hTargetLive
        hCurrent hFuture hLocal hWellFormed
  | right_complete_tock outer leftEnv interface left left' right leftLabel leftCurrent
      leftFuture hRightSkip hLeftLive hLeftOffers hTargetLive hCurrent hFuture
      hLocal hWellFormed _ ih =>
      exact .right_complete outer leftEnv interface left left' right leftLabel
        leftCurrent leftFuture hRightSkip hLeftLive ih hLeftOffers hTargetLive
        hCurrent hFuture hLocal hWellFormed

/-- An offers derivation and its underlying transition form a decorated step. -/
theorem TypeOffers.toDecorated {env : TypeEnvironment} {source : PactType}
    {label : TypeLabel} {target : PactType} {current future : Finset BareMessage}
    (h : TypeOffers env source label target current future) :
    DecoratedTypeTransition env source label { current := current, future := future }
      target :=
  ⟨h.toTransition, h⟩

end Pact
