import Anvilpp.ProofHelpers.Inference.ParallelLifting

/-!
# Decorated steps lift

The paper's helper: an abstract decorated step at a reachable residual is
realised by a concrete step exposing the erased current offer and the same
future component.  The concrete target need not abstract to the recorded one —
a conditional takes the branch its own guard selects — and the concrete label
agrees with the recorded one except in fair-choice outcomes.
-/

namespace Pact

noncomputable section

open Classical

/-! ## Environments -/

theorem clock_of_eraseEnvironment {env : Environment} {typeEnv : TypeEnvironment}
    (h : eraseEnvironment env = typeEnv) : env.clock = typeEnv.clock := by
  rw [← h]; rfl

theorem LocalTypeOfferEnvironment.clock_false
    {outer siblingEnv localEnv : TypeEnvironment} {interface : Interface}
    {localType : PactType} {current future : Finset BareMessage}
    (hLocal : LocalTypeOfferEnvironment outer interface localType siblingEnv
      current future localEnv) (hOuter : outer.clock = false) :
    localEnv.clock = false := by
  cases hLocal with
  | clock _ _ _ _ hClockOuter => exact absurd hClockOuter (by rw [hOuter]; simp)
  | ordinary _ _ _ _ _ _ _ _ hLocalClock _ _ => exact hLocalClock

/-- Under a non-clock environment no type step observes the clock. -/
theorem TypeOffers.label_ne_tock {env : TypeEnvironment} {source target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hClock : env.clock = false) : label ≠ TypeLabel.tock := by
  induction hOffers with
  | action _ _ _ _ _ => simp [TypeLabel.message]
  | action_wait _ _ _ _ _ => simp [TypeLabel.silent]
  | choice_left _ _ _ _ _ => simp [TypeLabel.silent]
  | choice_right _ _ _ _ _ => simp [TypeLabel.silent]
  | fair_left _ _ _ _ _ _ => simp [TypeLabel.fair]
  | fair_right _ _ _ _ _ _ => simp [TypeLabel.fair]
  | cycle _ _ hPrem => exact absurd hPrem.2 (by rw [hClock]; simp)
  | cycle_wait _ _ _ => simp [TypeLabel.silent]
  | skip _ _ _ => simp [TypeLabel.silent]
  | progress _ _ _ _ => simp [TypeLabel.progress]
  | recur _ _ _ _ _ => simp [TypeLabel.silent]
  | seq _ _ _ _ _ _ _ _ _ _ hTock _ => exact hTock
  | seq_tock _ _ _ _ _ _ _ _ _ ih => exact absurd rfl (ih hClock)
  | seq_fuse _ _ _ _ _ _ _ _ _ hTock _ => exact hTock
  | seq_fuse_tock _ _ _ _ _ _ _ _ ih => exact absurd rfl (ih hClock)
  | xoffer_branch _ _ _ _ _ _ _ => simp [TypeLabel.message]
  | xoffer_else _ _ _ _ _ => simp [TypeLabel.silent]
  | xoffer_wait _ _ _ _ _ => simp [TypeLabel.silent]
  | offer_some _ _ _ _ _ _ => simp [TypeLabel.silent]
  | offer_else _ _ _ _ _ => simp [TypeLabel.silent]
  | offer_wait _ _ _ _ _ => simp [TypeLabel.silent]
  | par _ _ _ interface _ _ _ _ _ leftLabel rightLabel _ _ _ _ _ _ _ _ _
      hLocalLeft _ _ ihLeft _ =>
      intro hAbsurd
      exact ihLeft (hLocalLeft.clock_false hClock)
        (((TypeLabel.combine_eq_tock_iff interface leftLabel rightLabel).1 hAbsurd).1)
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ _ => exact hNotTock
  | par_fuse_tock _ _ _ interface _ _ _ leftLabel rightLabel _ _ _ _ _ _
      hLocalLeft _ _ hTock ihLeft _ =>
      exact absurd (((TypeLabel.combine_eq_tock_iff interface leftLabel
        rightLabel).1 hTock).1) (ihLeft (hLocalLeft.clock_false hClock))
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocalRight _ _ _
      ihRight => exact ihRight (hLocalRight.clock_false hClock)
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocalLeft _ _ _ _
      ihLeft => exact ihLeft (hLocalLeft.clock_false hClock)

/-- The concrete sibling-local environment, formed from the projected parent
environment and the restored sibling current offers. -/
def localEnvironment (outer : Environment) (interface : Interface)
    (siblingCurrent : Finset Offer) (siblingFuture : Finset BareMessage) :
    Environment :=
  { immediate := outer.immediate ∪ restrictCurrent interface siblingCurrent
    future := (outer.future ∪ restrictFuture interface siblingFuture) \
      (outer.immediate ∪ restrictCurrent interface siblingCurrent).image Offer.bare
    clock := false }

@[simp] theorem localEnvironment_clock (outer : Environment) (interface : Interface)
    (siblingCurrent : Finset Offer) (siblingFuture : Finset BareMessage) :
    (localEnvironment outer interface siblingCurrent siblingFuture).clock = false :=
  rfl

theorem localOfferEnvironment_localEnvironment {outer siblingEnv : Environment}
    (interface : Interface) (localProc : Proc) (siblingCurrent : Finset Offer)
    (siblingFuture : Finset BareMessage) (hOuter : outer.clock = false)
    (hSibling : siblingEnv.clock = false) :
    LocalOfferEnvironment outer interface localProc siblingEnv siblingCurrent
      siblingFuture
      (localEnvironment outer interface siblingCurrent siblingFuture) :=
  LocalOfferEnvironment.ordinary _ _ _ _ _ _ _ hOuter hSibling rfl rfl rfl

/-- The ordinary sibling-local type environment is determined by the parent
environment and the sibling's own offers. -/
theorem localTypeOfferEnvironment_eq {outer siblingEnv localEnv : TypeEnvironment}
    {interface : Interface} {localType : PactType}
    {current future : Finset BareMessage}
    (hLocal : LocalTypeOfferEnvironment outer interface localType siblingEnv
      current future localEnv) (hOuter : outer.clock = false) :
    localEnv =
      { immediate := outer.immediate ∪ restrictTypeOffers interface current
        future := (outer.future ∪ restrictTypeOffers interface future) \
          (outer.immediate ∪ restrictTypeOffers interface current)
        clock := false } := by
  cases hLocal with
  | clock _ _ _ _ hClockOuter => exact absurd hClockOuter (by rw [hOuter]; simp)
  | ordinary _ _ _ _ _ _ _ _ hClock hImmediate hFuture =>
      cases localEnv with
      | mk immediate future clock =>
          simp only at hImmediate hFuture hClock
          subst hClock; subst hImmediate
          simp only [TypeEnvironment.mk.injEq]
          exact ⟨trivial, hFuture, trivial⟩

theorem eraseEnvironment_localEnvironment (outer : Environment)
    (interface : Interface) (siblingCurrent : Finset Offer)
    (siblingFuture : Finset BareMessage) :
    eraseEnvironment (localEnvironment outer interface siblingCurrent siblingFuture) =
      { immediate := (eraseEnvironment outer).immediate ∪
          restrictTypeOffers interface (siblingCurrent.image Offer.bare)
        future := ((eraseEnvironment outer).future ∪
            restrictTypeOffers interface siblingFuture) \
          ((eraseEnvironment outer).immediate ∪
            restrictTypeOffers interface (siblingCurrent.image Offer.bare))
        clock := false } := by
  simp only [eraseEnvironment, localEnvironment, Environment.bareImmediate,
    Finset.image_union, image_restrictCurrent, restrictFuture_eq,
    ]

/-! ## Agreement at the atomic labels -/

theorem labelAgree_silent : LabelAgree TypeLabel.silent Label.silent := by
  rw [← eraseLabel_silent]; exact labelAgree_eraseLabel _

theorem labelAgree_message (msg : MessageId) (dir : MessageDir) (value : Bool) :
    LabelAgree (TypeLabel.message msg dir) (Label.message msg dir value) := by
  rw [← eraseLabel_message msg dir value]; exact labelAgree_eraseLabel _

theorem labelAgree_progress (pid : ProcId) :
    LabelAgree (TypeLabel.progress pid) (Label.progress pid) := by
  rw [← eraseLabel_progress pid]; exact labelAgree_eraseLabel _

/-- A fair conditional keeps its own outcome; the labels still agree on every
message observation and on the clock. -/
theorem labelAgree_fair (bid : BranchId) (typeTaken taken : Bool) :
    LabelAgree (TypeLabel.fair bid typeTaken) (Label.fair bid taken) := by
  refine ⟨?_, ?_, ?_⟩
  · ext msg
    simp only [TypeLabel.fair, Label.fair, TypeLabel.sends, Label.sends,
      TypeLabel.messageIdsWith, Label.messageIdsWith, Finset.mem_image,
      Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨o, ⟨rfl, hDir⟩, -⟩; exact hDir.elim
    · rintro ⟨o, ⟨rfl, hDir⟩, -⟩; exact hDir.elim
  · ext msg
    simp only [TypeLabel.fair, Label.fair, TypeLabel.recvs, Label.recvs,
      TypeLabel.messageIdsWith, Label.messageIdsWith, Finset.mem_image,
      Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨o, ⟨rfl, hDir⟩, -⟩; exact hDir.elim
    · rintro ⟨o, ⟨rfl, hDir⟩, -⟩; exact hDir.elim
  · simp [TypeLabel.fair, Label.fair, TypeLabel.isTock, Label.isTock]

/-! ## Environment transfer -/

theorem wellFormed_of_erase {env : Environment} {typeEnv : TypeEnvironment}
    {alphabet : PactTypeAlphabet} (hErase : eraseEnvironment env = typeEnv)
    (hWF : typeEnv.WellFormed alphabet) : env.WellFormed alphabet :=
  (environment_wellFormed_iff env alphabet).2 (by rw [hErase]; exact hWF)

theorem hasRecv_of_erase {env : Environment} {typeEnv : TypeEnvironment}
    {msg : MessageId} (hErase : eraseEnvironment env = typeEnv)
    (hNeed : typeEnv.hasNeed (msg, MessageDir.send)) : env.hasRecv msg :=
  (hasNeed_send_iff env msg).1 (by rw [hErase]; exact hNeed)

theorem hasSend_of_erase {env : Environment} {typeEnv : TypeEnvironment}
    {msg : MessageId} (hErase : eraseEnvironment env = typeEnv)
    (hNeed : typeEnv.hasNeed (msg, MessageDir.recv)) : ∃ value, env.hasSend msg value :=
  (hasNeed_recv_iff env msg).1 (by rw [hErase]; exact hNeed)

/-! ## The waiting set depends only on the future menu -/

def waitingOfferSetOf (futureMenu : Finset BareMessage)
    (branches : List ChoiceBranch) : Finset Offer :=
  ((branches.filter fun branch =>
      decide (ChoiceBranch.action branch ∈
        (futureMenu.image bareNeed ∩ branchActions branches))).map
    ChoiceBranch.offer).toFinset

theorem waitingOfferSet_eq_of (env : Environment) (branches : List ChoiceBranch) :
    waitingOfferSet env branches = waitingOfferSetOf env.future branches := rfl

theorem waitingOfferSetOf_image (futureMenu : Finset BareMessage)
    (branches : List ChoiceBranch) :
    (waitingOfferSetOf futureMenu branches).image Offer.bare =
      futureMenu.image bareNeed ∩ branchActions branches := by
  have := waitingOfferSet_image
    { immediate := ∅, future := futureMenu, clock := false } branches
  rw [waitingOfferSet_eq_of] at this
  exact this

theorem TypeOffers.skip_inversion {env : TypeEnvironment}
    {alphabet : PactTypeAlphabet} {label : TypeLabel} {target : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.skip alphabet) label target current future) :
    label = TypeLabel.silent ∧ target = .skip alphabet ∧ current = ∅ ∧
      future = ∅ ∧ env.clock = false := by
  cases hOffers with
  | skip _ _ hPrem => exact ⟨rfl, rfl, rfl, typeFutureOffers_skip alphabet, hPrem.2⟩

/-! ## The lifting induction -/

theorem lifting_core :
    ∀ {typeEnv : TypeEnvironment} {source typeTarget : PactType}
      {typeLabel : TypeLabel} {current future : Finset BareMessage},
      TypeOffers typeEnv source typeLabel typeTarget current future →
      ∀ process : Proc, inferProcess process = source → typeEnv.clock = false →
        Proc.AlphabetWellFormed process → Proc.ConjunctRegular process →
        DataWFProc process →
        ∃ processCurrent : Finset Offer,
          processCurrent.image Offer.bare = current ∧
          ∀ env : Environment, eraseEnvironment env = typeEnv →
            ∃ processTarget processLabel,
              Offers env process processLabel processTarget processCurrent future ∧
              LabelAgree typeLabel processLabel := by
  intro typeEnv source typeTarget typeLabel current future hOffers
  induction hOffers with
  | action _ _ _ _ _ =>
      intro process hShape _ _ _ _
      exact (inferProcess_eq_message hShape).elim
  | action_wait _ _ _ _ _ =>
      intro process hShape _ _ _ _
      exact (inferProcess_eq_message hShape).elim
  | choice_left typeEnv alphabet left right hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨expr, l, r, rfl, rfl, rfl⟩ := inferProcess_eq_choice hShape
      refine ⟨∅, by simp, ?_⟩
      intro env hErase
      rw [dataWFProc_ifunfair_iff] at hData
      obtain ⟨value, hValue⟩ := exprEval_of_closed expr hData.1
      have hEnvWF := wellFormed_of_erase hErase hPrem.1
      have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
      have hFuture : procFutureOffers (Proc.ifunfair alphabet expr l r) =
          typeFutureOffers (.choice alphabet (inferProcess l) (inferProcess r)) := by
        rw [procFutureOffers_inferProcess, inferProcess]
      rw [← hFuture]
      cases value with
      | true =>
          exact ⟨l, Label.silent,
            Offers.if_true env alphabet expr l r ⟨hEnvWF, hEnvClock, hValue⟩,
            labelAgree_silent⟩
      | false =>
          exact ⟨r, Label.silent,
            Offers.if_false env alphabet expr l r ⟨hEnvWF, hEnvClock, hValue⟩,
            labelAgree_silent⟩
  | choice_right typeEnv alphabet left right hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨expr, l, r, rfl, rfl, rfl⟩ := inferProcess_eq_choice hShape
      refine ⟨∅, by simp, ?_⟩
      intro env hErase
      rw [dataWFProc_ifunfair_iff] at hData
      obtain ⟨value, hValue⟩ := exprEval_of_closed expr hData.1
      have hEnvWF := wellFormed_of_erase hErase hPrem.1
      have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
      have hFuture : procFutureOffers (Proc.ifunfair alphabet expr l r) =
          typeFutureOffers (.choice alphabet (inferProcess l) (inferProcess r)) := by
        rw [procFutureOffers_inferProcess, inferProcess]
      rw [← hFuture]
      cases value with
      | true =>
          exact ⟨l, Label.silent,
            Offers.if_true env alphabet expr l r ⟨hEnvWF, hEnvClock, hValue⟩,
            labelAgree_silent⟩
      | false =>
          exact ⟨r, Label.silent,
            Offers.if_false env alphabet expr l r ⟨hEnvWF, hEnvClock, hValue⟩,
            labelAgree_silent⟩
  | fair_left typeEnv alphabet bid left right hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨expr, l, r, rfl, rfl, rfl⟩ := inferProcess_eq_fairChoice hShape
      refine ⟨∅, by simp, ?_⟩
      intro env hErase
      rw [dataWFProc_iffair_iff] at hData
      obtain ⟨value, hValue⟩ := exprEval_of_closed expr hData.1
      have hEnvWF := wellFormed_of_erase hErase hPrem.1
      have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
      have hFuture : procFutureOffers (Proc.iffair alphabet bid expr l r) =
          typeFutureOffers
            (.fairChoice alphabet bid (inferProcess l) (inferProcess r)) := by
        rw [procFutureOffers_inferProcess, inferProcess]
      rw [← hFuture]
      cases value with
      | true =>
          exact ⟨l, Label.fair bid true,
            Offers.fair_true env alphabet bid expr l r ⟨hEnvWF, hEnvClock, hValue⟩,
            labelAgree_fair bid true true⟩
      | false =>
          exact ⟨r, Label.fair bid false,
            Offers.fair_false env alphabet bid expr l r ⟨hEnvWF, hEnvClock, hValue⟩,
            labelAgree_fair bid true false⟩
  | fair_right typeEnv alphabet bid left right hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨expr, l, r, rfl, rfl, rfl⟩ := inferProcess_eq_fairChoice hShape
      refine ⟨∅, by simp, ?_⟩
      intro env hErase
      rw [dataWFProc_iffair_iff] at hData
      obtain ⟨value, hValue⟩ := exprEval_of_closed expr hData.1
      have hEnvWF := wellFormed_of_erase hErase hPrem.1
      have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
      have hFuture : procFutureOffers (Proc.iffair alphabet bid expr l r) =
          typeFutureOffers
            (.fairChoice alphabet bid (inferProcess l) (inferProcess r)) := by
        rw [procFutureOffers_inferProcess, inferProcess]
      rw [← hFuture]
      cases value with
      | true =>
          exact ⟨l, Label.fair bid true,
            Offers.fair_true env alphabet bid expr l r ⟨hEnvWF, hEnvClock, hValue⟩,
            labelAgree_fair bid false true⟩
      | false =>
          exact ⟨r, Label.fair bid false,
            Offers.fair_false env alphabet bid expr l r ⟨hEnvWF, hEnvClock, hValue⟩,
            labelAgree_fair bid false false⟩
  | cycle typeEnv alphabet hPrem =>
      intro process hShape hClock hAlpha hConj hData
      exact absurd hPrem.2 (by rw [hClock]; simp)
  | cycle_wait typeEnv alphabet hPrem =>
      intro process hShape hClock hAlpha hConj hData
      rw [inferProcess_eq_tock hShape]
      refine ⟨∅, by simp, ?_⟩
      intro env hErase
      have hFuture : procFutureOffers (Proc.cycle alphabet) =
          typeFutureOffers (.tock alphabet) := by
        rw [procFutureOffers_inferProcess, inferProcess]
      rw [← hFuture]
      exact ⟨Proc.cycle alphabet, Label.silent,
        Offers.cycle_wait env alphabet
          ⟨wellFormed_of_erase hErase hPrem.1,
            (clock_of_eraseEnvironment hErase).trans hClock⟩,
        labelAgree_silent⟩
  | skip typeEnv alphabet hPrem =>
      intro process hShape hClock hAlpha hConj hData
      rw [(inferProcess_eq_skip_iff process alphabet).1 hShape]
      refine ⟨∅, by simp, ?_⟩
      intro env hErase
      have hFuture : procFutureOffers (Proc.skip alphabet) =
          typeFutureOffers (.skip alphabet) := by
        rw [procFutureOffers_inferProcess, inferProcess]
      rw [← hFuture]
      exact ⟨Proc.skip alphabet, Label.silent,
        Offers.skip env alphabet
          ⟨wellFormed_of_erase hErase hPrem.1,
            (clock_of_eraseEnvironment hErase).trans hClock⟩,
        labelAgree_silent⟩
  | progress typeEnv alphabet pid hPrem =>
      intro process hShape hClock hAlpha hConj hData
      rw [inferProcess_eq_progress hShape]
      refine ⟨∅, by simp, ?_⟩
      intro env hErase
      have hFuture : procFutureOffers (Proc.skip alphabet) =
          typeFutureOffers (.skip alphabet) := by
        rw [procFutureOffers_inferProcess, inferProcess]
      rw [← hFuture]
      exact ⟨Proc.skip alphabet, Label.progress pid,
        Offers.progress env alphabet pid
          ⟨wellFormed_of_erase hErase hPrem.1,
            (clock_of_eraseEnvironment hErase).trans hClock⟩,
        labelAgree_progress pid⟩
  | recur typeEnv alphabet name body hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨b, rfl, rfl⟩ := inferProcess_eq_recur hShape
      refine ⟨∅, by simp, ?_⟩
      intro env hErase
      have hFuture : procFutureOffers
            (Semantics.procReplace b name (Proc.recur alphabet name b)) =
          typeFutureOffers ((inferProcess b).replaceVar name
            (.recur alphabet name (inferProcess b))) := by
        rw [procFutureOffers_inferProcess, inferProcess_procReplace, inferProcess]
      rw [← hFuture]
      exact ⟨_, Label.silent,
        Offers.recur env alphabet name b
          ⟨wellFormed_of_erase hErase hPrem.1,
            (clock_of_eraseEnvironment hErase).trans hClock⟩,
        labelAgree_silent⟩
  | xoffer_branch typeEnv alphabet elseType branches action processType hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨elseProcess, procBranches, rfl, rfl, rfl⟩ := inferProcess_eq_xoffer hShape
      obtain ⟨branch, hMem, hEq⟩ := exists_branch_of_mem_inferBranches hPrem.2.1
      have hFuture :
          procFutureOffers (Proc.xoffer alphabet elseProcess procBranches) \
              branchActions procBranches =
            typeFutureOffers (.xoffer alphabet (inferProcess elseProcess)
                (inferBranches procBranches)) \
              typeBranchActions (inferBranches procBranches) := by
        rw [procFutureOffers_inferProcess, inferProcess,
          typeBranchActions_inferBranches]
      rw [dataWFProc_xoffer_iff] at hData
      have hBranchBound := branchBound_of_mem hData.2 hMem
      cases branch with
      | send m expr p =>
          have hAction : action = (m, MessageDir.send) := (congrArg Prod.fst hEq).symm
          rw [BranchBound] at hBranchBound
          obtain ⟨value, hValue⟩ := exprEval_of_closed expr hBranchBound.1
          subst hAction
          refine ⟨{Offer.send m value}, by simp [Offer.bare], ?_⟩
          intro env hErase
          rw [← hFuture]
          exact ⟨p, Label.message m MessageDir.send value,
            Offers.xoffer_send env alphabet elseProcess procBranches m expr p value
              ⟨wellFormed_of_erase hErase hPrem.1, hMem,
                hasRecv_of_erase hErase hPrem.2.2.1, hValue,
                (typeResolved_iff env procBranches).1
                  (by rw [hErase]; exact hPrem.2.2.2)⟩,
            labelAgree_message m MessageDir.send value⟩
      | recv m varName p =>
          have hAction : action = (m, MessageDir.recv) := (congrArg Prod.fst hEq).symm
          subst hAction
          refine ⟨{Offer.recv m}, by simp [Offer.bare], ?_⟩
          intro env hErase
          obtain ⟨value, hValue⟩ := hasSend_of_erase hErase hPrem.2.2.1
          rw [← hFuture]
          exact ⟨_, Label.message m MessageDir.recv value,
            Offers.xoffer_recv env alphabet elseProcess procBranches m varName p value
              ⟨wellFormed_of_erase hErase hPrem.1, hMem, hValue,
                (typeResolved_iff env procBranches).1
                  (by rw [hErase]; exact hPrem.2.2.2)⟩,
            labelAgree_message m MessageDir.recv value⟩
  | xoffer_else typeEnv alphabet elseType branches hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨elseProcess, procBranches, rfl, rfl, rfl⟩ := inferProcess_eq_xoffer hShape
      refine ⟨projectCurrent alphabet (branchOfferSet procBranches), ?_, ?_⟩
      · rw [projectCurrent_image, branchOfferSet_image, typeBranchActions_inferBranches]
      intro env hErase
      have hFuture :
          procFutureOffers (Proc.xoffer alphabet elseProcess procBranches) \
              branchActions procBranches =
            typeFutureOffers (.xoffer alphabet (inferProcess elseProcess)
                (inferBranches procBranches)) \
              typeBranchActions (inferBranches procBranches) := by
        rw [procFutureOffers_inferProcess, inferProcess,
          typeBranchActions_inferBranches]
      rw [← hFuture]
      exact ⟨elseProcess, Label.silent,
        Offers.xoffer_else env alphabet elseProcess procBranches
          ⟨wellFormed_of_erase hErase hPrem.1,
            (clock_of_eraseEnvironment hErase).trans hClock,
            (typeNoImmediateBranch_iff env procBranches).1
              (by rw [hErase]; exact hPrem.2.2.1),
            (typeResolved_iff env procBranches).1
              (by rw [hErase]; exact hPrem.2.2.2)⟩,
        labelAgree_silent⟩
  | xoffer_wait typeEnv alphabet elseType branches hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨elseProcess, procBranches, rfl, rfl, rfl⟩ := inferProcess_eq_xoffer hShape
      refine ⟨waitingOfferSetOf typeEnv.future procBranches, ?_, ?_⟩
      · rw [waitingOfferSetOf_image, typeWaitingOffers,
          typeBranchActions_inferBranches, bareNeed_eq_typeNeed]
      · intro env hErase
        have hFutureEq : env.future = typeEnv.future := by rw [← hErase]; rfl
        have hCurrent : waitingOfferSetOf typeEnv.future procBranches =
            waitingOfferSet env procBranches := by
          rw [waitingOfferSet_eq_of, hFutureEq]
        have hFuture :
            procFutureOffers (Proc.xoffer alphabet elseProcess procBranches) \
                waitingOffers env procBranches =
              typeFutureOffers (.xoffer alphabet (inferProcess elseProcess)
                  (inferBranches procBranches)) \
                typeWaitingOffers typeEnv (inferBranches procBranches) := by
          rw [procFutureOffers_inferProcess, inferProcess, ← hErase,
            typeWaitingOffers_eq]
        rw [← hFuture, hCurrent]
        exact ⟨_, Label.silent,
          Offers.xoffer_wait env alphabet elseProcess procBranches
            ⟨wellFormed_of_erase hErase hPrem.1,
              fun h => hPrem.2.1
                (by rw [← hErase]; exact (typeResolved_iff env procBranches).2 h),
              (clock_of_eraseEnvironment hErase).trans hClock⟩,
          labelAgree_silent⟩
  | offer_some typeEnv alphabet elseType branches enabled hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨elseProcess, procBranches, rfl, rfl, rfl⟩ := inferProcess_eq_offer hShape
      obtain ⟨branch, hMem, hEq⟩ := exists_branch_of_mem_inferBranches hPrem.2.1
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      have hCommit := inferProcess_parallelProcessBranchesSelecting
        hAlpha.2.2.2 hConj.1 hMem
      refine ⟨∅, by simp, ?_⟩
      intro env hErase
      have hFuture :
          procFutureOffers
              (parallelProcessBranchesSelecting alphabet branch procBranches) =
            typeFutureOffers
              (parallelTypeBranchesSelecting alphabet enabled
                (inferBranches procBranches)) := by
        rw [procFutureOffers_inferProcess, hCommit, hEq]
      rw [← hFuture]
      exact ⟨_, Label.silent,
        Offers.offer_some env alphabet elseProcess procBranches branch
          ⟨wellFormed_of_erase hErase hPrem.1, hMem,
            (typeBranchEnabled_iff env branch).1
              (by rw [hErase, hEq]; exact hPrem.2.2)⟩,
        labelAgree_silent⟩
  | offer_else typeEnv alphabet elseType branches hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨elseProcess, procBranches, rfl, rfl, rfl⟩ := inferProcess_eq_offer hShape
      refine ⟨projectCurrent alphabet (branchOfferSet procBranches), ?_, ?_⟩
      · rw [projectCurrent_image, branchOfferSet_image, typeBranchActions_inferBranches]
      · intro env hErase
        have hFuture :
            procFutureOffers elseProcess \ (branchActions procBranches ∩ alphabet.actions) =
              typeFutureOffers (inferProcess elseProcess) \
                (typeBranchActions (inferBranches procBranches) ∩ alphabet.actions) := by
          rw [procFutureOffers_inferProcess, typeBranchActions_inferBranches]
        rw [← hFuture]
        exact ⟨elseProcess, Label.silent,
          Offers.offer_else env alphabet elseProcess procBranches
            ⟨wellFormed_of_erase hErase hPrem.1,
              (clock_of_eraseEnvironment hErase).trans hClock,
              (typeNoImmediateBranch_iff env procBranches).1
                (by rw [hErase]; exact hPrem.2.2.1),
              (typeResolved_iff env procBranches).1
                (by rw [hErase]; exact hPrem.2.2.2)⟩,
          labelAgree_silent⟩
  | offer_wait typeEnv alphabet elseType branches hPrem =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨elseProcess, procBranches, rfl, rfl, rfl⟩ := inferProcess_eq_offer hShape
      refine ⟨projectCurrent alphabet (branchOfferSet procBranches), ?_, ?_⟩
      · rw [projectCurrent_image, branchOfferSet_image, typeBranchActions_inferBranches]
      · intro env hErase
        have hFuture :
            procFutureOffers (Proc.offer alphabet elseProcess procBranches) \
                (branchActions procBranches ∩ alphabet.actions) =
              typeFutureOffers (.offer alphabet (inferProcess elseProcess)
                  (inferBranches procBranches)) \
                (typeBranchActions (inferBranches procBranches) ∩ alphabet.actions) := by
          rw [procFutureOffers_inferProcess, inferProcess,
            typeBranchActions_inferBranches]
        rw [← hFuture]
        exact ⟨_, Label.silent,
          Offers.offer_wait env alphabet elseProcess procBranches
            ⟨wellFormed_of_erase hErase hPrem.1,
              (clock_of_eraseEnvironment hErase).trans hClock,
              (typeNoImmediateBranch_iff env procBranches).1
                (by rw [hErase]; exact hPrem.2.2.1),
              fun h => hPrem.2.2.2
                (by rw [← hErase]; exact (typeResolved_iff env procBranches).2 h)⟩,
          labelAgree_silent⟩
  | seq typeEnv alphabet left left' right label current childFuture hLeft hSkip
      hTock ih =>
      intro process hShape hClock hAlpha hConj hData
      rcases inferProcess_eq_seq hShape with
        ⟨m, expr, p, rfl, rfl, rfl⟩ | ⟨m, varName, p, rfl, rfl, rfl⟩ |
          ⟨varName, expr, p, rfl, rfl, rfl⟩ | ⟨p₁, p₂, rfl, rfl, rfl⟩
      · -- a send prefix: its atomic left operand must be waiting
        cases hLeft with
        | action _ _ _ _ hPrem => exact absurd rfl hSkip
        | action_wait _ _ _ _ hPrem =>
            rw [Proc.AlphabetWellFormed] at hAlpha
            rw [dataWFProc_send_iff] at hData
            obtain ⟨value, hValue⟩ := exprEval_of_closed expr hData.1
            refine ⟨projectCurrent alphabet {Offer.send m value},
              by simp [projectCurrent_image, Offer.bare], ?_⟩
            intro env hErase
            have hFuture :
                procFutureOffers (Proc.send alphabet m expr p) \
                    ({(m, MessageDir.send)} ∩ alphabet.actions) =
                  ((typeFutureOffers (.message alphabet m MessageDir.send) \
                      ({(m, MessageDir.send)} ∩ alphabet.actions)) ∪
                    sequenceRightMenu (.message alphabet m MessageDir.send)
                      (inferProcess p)) \ ({(m, MessageDir.send)} ∩ alphabet.actions) := by
              rw [sdiff_union_sdiff, procFutureOffers_inferProcess, inferProcess,
                typeFutureOffers_sequence]
              simp only [canCompleteDeclared_message, ↓reduceIte, sequenceRightMenu]
            rw [← hFuture]
            exact ⟨_, Label.silent,
              Offers.send_wait env alphabet m expr p value
                ⟨wellFormed_of_erase hErase hPrem.1,
                  fun h => hPrem.2.1
                    (by rw [← hErase]; exact (hasNeed_send_iff env m).2 h),
                  (clock_of_eraseEnvironment hErase).trans hClock, hValue⟩,
              labelAgree_silent⟩
      · -- a receive prefix
        cases hLeft with
        | action _ _ _ _ hPrem => exact absurd rfl hSkip
        | action_wait _ _ _ _ hPrem =>
            rw [Proc.AlphabetWellFormed] at hAlpha
            refine ⟨projectCurrent alphabet {Offer.recv m},
              by simp [projectCurrent_image, Offer.bare], ?_⟩
            intro env hErase
            have hFuture :
                procFutureOffers (Proc.recv alphabet m varName p) \
                    ({(m, MessageDir.recv)} ∩ alphabet.actions) =
                  ((typeFutureOffers (.message alphabet m MessageDir.recv) \
                      ({(m, MessageDir.recv)} ∩ alphabet.actions)) ∪
                    sequenceRightMenu (.message alphabet m MessageDir.recv)
                      (inferProcess p)) \ ({(m, MessageDir.recv)} ∩ alphabet.actions) := by
              rw [sdiff_union_sdiff, procFutureOffers_inferProcess, inferProcess,
                typeFutureOffers_sequence]
              simp only [canCompleteDeclared_message, ↓reduceIte, sequenceRightMenu]
            rw [← hFuture]
            exact ⟨_, Label.silent,
              Offers.recv_wait env alphabet m varName p
                ⟨wellFormed_of_erase hErase hPrem.1,
                  fun value hValue => hPrem.2.1
                    (by rw [← hErase]; exact (hasNeed_recv_iff env m).2 ⟨value, hValue⟩),
                  (clock_of_eraseEnvironment hErase).trans hClock⟩,
              labelAgree_silent⟩
      · -- a local binding: its atomic `skip` cannot avoid completing
        cases hLeft with
        | skip _ _ hPrem => exact absurd rfl hSkip
      · -- a written sequence
        rw [Proc.AlphabetWellFormed] at hAlpha
        rw [Proc.ConjunctRegular] at hConj
        rw [dataWFProc_seq_iff] at hData
        obtain ⟨processCurrent, hImage, hLift⟩ :=
          ih p₁ rfl hClock hAlpha.2.2.2.1 hConj.1 hData.1
        refine ⟨processCurrent, hImage, ?_⟩
        intro env hErase
        obtain ⟨target, procLabel, hStep, hAgree⟩ := hLift env hErase
        have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
        have hMenu : procSequenceRightMenu p₁ p₂ =
            sequenceRightMenu (inferProcess p₁) (inferProcess p₂) :=
          procSequenceRightMenu_inferProcess p₁ p₂
        rw [← hImage, ← hMenu]
        by_cases hTargetSkip : target = Proc.skip target.alphabet
        · refine ⟨p₂, procLabel, ?_, hAgree⟩
          rw [hTargetSkip] at hStep
          exact Offers.seq_fuse env alphabet target.alphabet p₁ p₂ procLabel
            processCurrent _ hStep (hStep.label_ne_tock hEnvClock)
        · exact ⟨Proc.seq alphabet target p₂, procLabel,
            Offers.seq env alphabet p₁ target p₂ procLabel processCurrent _ hStep
              hTargetSkip (hStep.label_ne_tock hEnvClock), hAgree⟩
  | seq_tock typeEnv alphabet left left' right current childFuture hLeft hSkip ih =>
      intro process hShape hClock hAlpha hConj hData
      exact absurd rfl (hLeft.label_ne_tock hClock)
  | seq_fuse_tock typeEnv alphabet skipAlphabet left right current childFuture
      hLeft ih =>
      intro process hShape hClock hAlpha hConj hData
      exact absurd rfl (hLeft.label_ne_tock hClock)
  | seq_fuse typeEnv alphabet skipAlphabet left right label current childFuture
      hLeft hTock ih =>
      intro process hShape hClock hAlpha hConj hData
      rcases inferProcess_eq_seq hShape with
        ⟨m, expr, p, rfl, rfl, rfl⟩ | ⟨m, varName, p, rfl, rfl, rfl⟩ |
          ⟨varName, expr, p, rfl, rfl, rfl⟩ | ⟨p₁, p₂, rfl, rfl, rfl⟩
      · cases hLeft with
        | action _ _ _ _ hPrem =>
            rw [Proc.AlphabetWellFormed] at hAlpha
            rw [dataWFProc_send_iff] at hData
            obtain ⟨value, hValue⟩ := exprEval_of_closed expr hData.1
            refine ⟨projectCurrent alphabet {Offer.send m value},
              by simp [projectCurrent_image, Offer.bare], ?_⟩
            intro env hErase
            have hFuture :
                procFutureOffers p \ ({(m, MessageDir.send)} ∩ alphabet.actions) =
                  ((typeFutureOffers (PactType.skip alphabet)) ∪
                    sequenceRightMenu (.message alphabet m MessageDir.send)
                      (inferProcess p)) \ ({(m, MessageDir.send)} ∩ alphabet.actions) := by
              simp only [typeFutureOffers_skip, Finset.empty_union,
                sequenceRightMenu, canCompleteDeclared_message, ↓reduceIte,
                procFutureOffers_inferProcess]
            rw [← hFuture]
            exact ⟨p, Label.message m MessageDir.send value,
              Offers.send env alphabet m expr p value
                ⟨wellFormed_of_erase hErase hPrem.1,
                  hasRecv_of_erase hErase hPrem.2, hValue⟩,
              labelAgree_message m MessageDir.send value⟩
      · cases hLeft with
        | action _ _ _ _ hPrem =>
            rw [Proc.AlphabetWellFormed] at hAlpha
            refine ⟨projectCurrent alphabet {Offer.recv m},
              by simp [projectCurrent_image, Offer.bare], ?_⟩
            intro env hErase
            obtain ⟨value, hValue⟩ := hasSend_of_erase hErase hPrem.2
            have hFuture :
                procFutureOffers (Semantics.procExprReplace p varName value) \
                    ({(m, MessageDir.recv)} ∩ alphabet.actions) =
                  ((typeFutureOffers (PactType.skip alphabet)) ∪
                    sequenceRightMenu (.message alphabet m MessageDir.recv)
                      (inferProcess p)) \ ({(m, MessageDir.recv)} ∩ alphabet.actions) := by
              simp only [typeFutureOffers_skip, Finset.empty_union,
                sequenceRightMenu, canCompleteDeclared_message, ↓reduceIte,
                procFutureOffers_inferProcess, inferProcess_procExprReplace]
            rw [← hFuture]
            exact ⟨_, Label.message m MessageDir.recv value,
              Offers.recv env alphabet m varName p value
                ⟨wellFormed_of_erase hErase hPrem.1, hValue⟩,
              labelAgree_message m MessageDir.recv value⟩
      · obtain ⟨hLabel, hTarget, hCurrent, hChildFuture, hTypeClock⟩ :=
          TypeOffers.skip_inversion hLeft
        rw [Proc.AlphabetWellFormed] at hAlpha
        rw [dataWFProc_letp_iff] at hData
        obtain ⟨value, hValue⟩ := exprEval_of_closed expr hData.1
        subst hLabel; subst hCurrent; subst hChildFuture
        refine ⟨∅, by simp, ?_⟩
        intro env hErase
        have hFuture :
            procFutureOffers (Semantics.procExprReplace p varName value) =
              ((∅ : Finset BareMessage) ∪
                sequenceRightMenu (PactType.skip alphabet) (inferProcess p)) \ ∅ := by
          simp only [Finset.empty_union, sequenceRightMenu, canCompleteDeclared_skip,
            if_pos, Finset.sdiff_empty, procFutureOffers_inferProcess, inferProcess_procExprReplace]
        rw [← hFuture]
        exact ⟨_, Label.silent,
          Offers.letp env alphabet varName expr p value
            ⟨wellFormed_of_erase hErase (by
                have := TypeOffers.skip_inversion hLeft
                exact (by cases hLeft with
                  | skip _ _ hPrem => exact hPrem.1)),
              (clock_of_eraseEnvironment hErase).trans hClock, hValue⟩,
          labelAgree_silent⟩
      · rw [Proc.AlphabetWellFormed] at hAlpha
        rw [Proc.ConjunctRegular] at hConj
        rw [dataWFProc_seq_iff] at hData
        obtain ⟨processCurrent, hImage, hLift⟩ :=
          ih p₁ rfl hClock hAlpha.2.2.2.1 hConj.1 hData.1
        refine ⟨processCurrent, hImage, ?_⟩
        intro env hErase
        obtain ⟨target, procLabel, hStep, hAgree⟩ := hLift env hErase
        have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
        have hMenu : procSequenceRightMenu p₁ p₂ =
            sequenceRightMenu (inferProcess p₁) (inferProcess p₂) :=
          procSequenceRightMenu_inferProcess p₁ p₂
        rw [← hImage, ← hMenu]
        by_cases hTargetSkip : target = Proc.skip target.alphabet
        · refine ⟨p₂, procLabel, ?_, hAgree⟩
          rw [hTargetSkip] at hStep
          exact Offers.seq_fuse env alphabet target.alphabet p₁ p₂ procLabel
            processCurrent _ hStep (hStep.label_ne_tock hEnvClock)
        · exact ⟨Proc.seq alphabet target p₂, procLabel,
            Offers.seq env alphabet p₁ target p₂ procLabel processCurrent _ hStep
              hTargetSkip (hStep.label_ne_tock hEnvClock), hAgree⟩
  | par typeEnv leftEnv rightEnv interface alphabet left left' right right'
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftSkip hRightSkip hLeftOffers hRightOffers hNotBoth hLocalLeft
      hLocalRight hEnv ihLeft ihRight =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨p₁, p₂, rfl, rfl, rfl⟩ := inferProcess_eq_par hShape
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      rw [dataWFProc_par_iff] at hData
      have hLeftClock := hLocalLeft.clock_false hClock
      have hRightClock := hLocalRight.clock_false hClock
      obtain ⟨leftOffers, hLeftImage, hLeftLift⟩ :=
        ihLeft p₁ rfl hLeftClock hAlpha.2.2.1 hConj.1 hData.1
      obtain ⟨rightOffers, hRightImage, hRightLift⟩ :=
        ihRight p₂ rfl hRightClock hAlpha.2.2.2 hConj.2 hData.2
      have hNotTock : TypeLabel.combine interface leftLabel rightLabel ≠
          TypeLabel.tock := fun hAbsurd =>
        hLeftOffers.label_ne_tock hLeftClock
          ((TypeLabel.combine_eq_tock_iff _ _ _).1 hAbsurd).1
      refine ⟨hideOfferSet interface (leftOffers ∪ rightOffers), ?_, ?_⟩
      · rw [image_hideOfferSet, Finset.image_union, hLeftImage, hRightImage]
      · intro env hErase
        have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
        have hEraseLeft : eraseEnvironment
            (localEnvironment env interface rightOffers rightFuture) = leftEnv := by
          rw [eraseEnvironment_localEnvironment, hErase, hRightImage,
            localTypeOfferEnvironment_eq hLocalLeft hClock]
        have hEraseRight : eraseEnvironment
            (localEnvironment env interface leftOffers leftFuture) = rightEnv := by
          rw [eraseEnvironment_localEnvironment, hErase, hLeftImage,
            localTypeOfferEnvironment_eq hLocalRight hClock]
        obtain ⟨t₁, α₁, hStep₁, hAgree₁⟩ := hLeftLift _ hEraseLeft
        obtain ⟨t₂, α₂, hStep₂, hAgree₂⟩ := hRightLift _ hEraseRight
        rw [if_neg hNotTock, ← hideProcOffers_eq]
        obtain ⟨target, hStep⟩ := par_lift hAlpha.2.2.1 hAlpha.2.2.2 hStep₁ hStep₂
          (localOfferEnvironment_localEnvironment interface p₁ rightOffers
            rightFuture hEnvClock rfl)
          (localOfferEnvironment_localEnvironment interface p₂ leftOffers
            leftFuture hEnvClock rfl)
          (wellFormed_of_erase hErase hEnv.1)
          (LabelAgree.sync hAgree₁ hAgree₂ hEnv.2) hEnvClock
        exact ⟨target, _, hStep, LabelAgree.combine hAgree₁ hAgree₂⟩
  | par_fuse typeEnv leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftOffers
      hRightOffers hLocalLeft hLocalRight hEnv hNotTock ihLeft ihRight =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨p₁, p₂, rfl, rfl, rfl⟩ := inferProcess_eq_par hShape
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      rw [dataWFProc_par_iff] at hData
      have hLeftClock := hLocalLeft.clock_false hClock
      have hRightClock := hLocalRight.clock_false hClock
      obtain ⟨leftOffers, hLeftImage, hLeftLift⟩ :=
        ihLeft p₁ rfl hLeftClock hAlpha.2.2.1 hConj.1 hData.1
      obtain ⟨rightOffers, hRightImage, hRightLift⟩ :=
        ihRight p₂ rfl hRightClock hAlpha.2.2.2 hConj.2 hData.2
      refine ⟨hideOfferSet interface (leftOffers ∪ rightOffers), ?_, ?_⟩
      · rw [image_hideOfferSet, Finset.image_union, hLeftImage, hRightImage]
      · intro env hErase
        have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
        have hEraseLeft : eraseEnvironment
            (localEnvironment env interface rightOffers rightFuture) = leftEnv := by
          rw [eraseEnvironment_localEnvironment, hErase, hRightImage,
            localTypeOfferEnvironment_eq hLocalLeft hClock]
        have hEraseRight : eraseEnvironment
            (localEnvironment env interface leftOffers leftFuture) = rightEnv := by
          rw [eraseEnvironment_localEnvironment, hErase, hLeftImage,
            localTypeOfferEnvironment_eq hLocalRight hClock]
        obtain ⟨t₁, α₁, hStep₁, hAgree₁⟩ := hLeftLift _ hEraseLeft
        obtain ⟨t₂, α₂, hStep₂, hAgree₂⟩ := hRightLift _ hEraseRight
        rw [← hideProcOffers_eq]
        obtain ⟨target, hStep⟩ := par_lift hAlpha.2.2.1 hAlpha.2.2.2 hStep₁ hStep₂
          (localOfferEnvironment_localEnvironment interface p₁ rightOffers
            rightFuture hEnvClock rfl)
          (localOfferEnvironment_localEnvironment interface p₂ leftOffers
            leftFuture hEnvClock rfl)
          (wellFormed_of_erase hErase hEnv.1)
          (LabelAgree.sync hAgree₁ hAgree₂ hEnv.2) hEnvClock
        exact ⟨target, _, hStep, LabelAgree.combine hAgree₁ hAgree₂⟩
  | par_fuse_tock typeEnv leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftOffers
      hRightOffers hLocalLeft hLocalRight hEnv hTock ihLeft ihRight =>
      intro process hShape hClock hAlpha hConj hData
      exact absurd (((TypeLabel.combine_eq_tock_iff interface leftLabel
        rightLabel).1 hTock).1)
        (hLeftOffers.label_ne_tock (hLocalLeft.clock_false hClock))
  | left_complete typeEnv leftEnv rightEnv interface alphabet left right right'
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftIsSkip
      hRightSkip hLeftOffers hRightOffers hTargetSkip hLocalLeft hLocalRight
      hOuterWF hSync ihLeft ihRight =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨p₁, p₂, rfl, rfl, rfl⟩ := inferProcess_eq_par hShape
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      rw [dataWFProc_par_iff] at hData
      have hLeftClock := hLocalLeft.clock_false hClock
      have hRightClock := hLocalRight.clock_false hClock
      obtain ⟨-, -, hLeftCurrent, hLeftFuture, -⟩ :=
        TypeOffers.skip_inversion (by rw [← hLeftIsSkip]; exact hLeftOffers)
      subst hLeftCurrent; subst hLeftFuture
      obtain ⟨leftOffers, hLeftImage, hLeftLift⟩ :=
        ihLeft p₁ rfl hLeftClock hAlpha.2.2.1 hConj.1 hData.1
      obtain ⟨rightOffers, hRightImage, hRightLift⟩ :=
        ihRight p₂ rfl hRightClock hAlpha.2.2.2 hConj.2 hData.2
      refine ⟨hideOfferSet interface (leftOffers ∪ rightOffers), ?_, ?_⟩
      · rw [image_hideOfferSet, Finset.image_union, hLeftImage, hRightImage,
          Finset.empty_union]
      · intro env hErase
        have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
        have hEraseLeft : eraseEnvironment
            (localEnvironment env interface rightOffers rightFuture) = leftEnv := by
          rw [eraseEnvironment_localEnvironment, hErase, hRightImage,
            localTypeOfferEnvironment_eq hLocalLeft hClock]
        have hEraseRight : eraseEnvironment
            (localEnvironment env interface leftOffers ∅) = rightEnv := by
          rw [eraseEnvironment_localEnvironment, hErase, hLeftImage,
            localTypeOfferEnvironment_eq hLocalRight hClock]
        obtain ⟨t₁, α₁, hStep₁, hAgree₁⟩ := hLeftLift _ hEraseLeft
        obtain ⟨t₂, α₂, hStep₂, hAgree₂⟩ := hRightLift _ hEraseRight
        obtain ⟨target, hStep⟩ := par_lift hAlpha.2.2.1 hAlpha.2.2.2 hStep₁ hStep₂
          (localOfferEnvironment_localEnvironment interface p₁ rightOffers
            rightFuture hEnvClock rfl)
          (localOfferEnvironment_localEnvironment interface p₂ leftOffers
            ∅ hEnvClock rfl)
          (wellFormed_of_erase hErase hOuterWF)
          (LabelAgree.sync hAgree₁ hAgree₂ hSync) hEnvClock
        rw [Finset.empty_union] at hStep
        have hAgree := LabelAgree.combine (interface := interface) hAgree₁ hAgree₂
        rw [TypeLabel.combine_silent_left interface rightLabel hSync] at hAgree
        rw [← hideProcOffers_eq]
        exact ⟨target, _, hStep, hAgree⟩
  | right_complete typeEnv leftEnv rightEnv interface alphabet left left' right
      leftLabel leftCurrent leftFuture rightCurrent rightFuture hRightIsSkip
      hLeftSkip hRightOffers hLeftOffers hTargetSkip hLocalLeft hLocalRight
      hOuterWF hSync ihRight ihLeft =>
      intro process hShape hClock hAlpha hConj hData
      obtain ⟨p₁, p₂, rfl, rfl, rfl⟩ := inferProcess_eq_par hShape
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      rw [dataWFProc_par_iff] at hData
      have hLeftClock := hLocalLeft.clock_false hClock
      have hRightClock := hLocalRight.clock_false hClock
      obtain ⟨-, -, hRightCurrent, hRightFuture, -⟩ :=
        TypeOffers.skip_inversion (by rw [← hRightIsSkip]; exact hRightOffers)
      subst hRightCurrent; subst hRightFuture
      obtain ⟨leftOffers, hLeftImage, hLeftLift⟩ :=
        ihLeft p₁ rfl hLeftClock hAlpha.2.2.1 hConj.1 hData.1
      obtain ⟨rightOffers, hRightImage, hRightLift⟩ :=
        ihRight p₂ rfl hRightClock hAlpha.2.2.2 hConj.2 hData.2
      refine ⟨hideOfferSet interface (leftOffers ∪ rightOffers), ?_, ?_⟩
      · rw [image_hideOfferSet, Finset.image_union, hLeftImage, hRightImage,
          Finset.union_empty]
      · intro env hErase
        have hEnvClock := (clock_of_eraseEnvironment hErase).trans hClock
        have hEraseLeft : eraseEnvironment
            (localEnvironment env interface rightOffers ∅) = leftEnv := by
          rw [eraseEnvironment_localEnvironment, hErase, hRightImage,
            localTypeOfferEnvironment_eq hLocalLeft hClock]
        have hEraseRight : eraseEnvironment
            (localEnvironment env interface leftOffers leftFuture) = rightEnv := by
          rw [eraseEnvironment_localEnvironment, hErase, hLeftImage,
            localTypeOfferEnvironment_eq hLocalRight hClock]
        obtain ⟨t₁, α₁, hStep₁, hAgree₁⟩ := hLeftLift _ hEraseLeft
        obtain ⟨t₂, α₂, hStep₂, hAgree₂⟩ := hRightLift _ hEraseRight
        obtain ⟨target, hStep⟩ := par_lift hAlpha.2.2.1 hAlpha.2.2.2 hStep₁ hStep₂
          (localOfferEnvironment_localEnvironment interface p₁ rightOffers
            ∅ hEnvClock rfl)
          (localOfferEnvironment_localEnvironment interface p₂ leftOffers
            leftFuture hEnvClock rfl)
          (wellFormed_of_erase hErase hOuterWF)
          (LabelAgree.sync hAgree₁ hAgree₂ hSync) hEnvClock
        rw [Finset.union_empty] at hStep
        have hAgree := LabelAgree.combine (interface := interface) hAgree₁ hAgree₂
        rw [TypeLabel.combine_silent_right interface leftLabel hSync] at hAgree
        rw [← hideProcOffers_eq]
        exact ⟨target, _, hStep, hAgree⟩

/-! ## The clock environment -/

theorem LocalTypeOfferEnvironment.tock_of_clock
    {outer siblingEnv localEnv : TypeEnvironment} {interface : Interface}
    {localType : PactType} {current future : Finset BareMessage}
    (hLocal : LocalTypeOfferEnvironment outer interface localType siblingEnv
      current future localEnv) (hOuter : outer.clock = true) :
    localEnv = TypeEnvironment.tock := by
  cases hLocal with
  | clock _ _ _ _ _ => rfl
  | ordinary _ _ _ _ _ _ hOuterClock _ _ _ _ =>
      exact absurd hOuterClock (by rw [hOuter]; simp)

/-- Under the clock environment every type step is a clock step with the empty
offer pair. -/
theorem TypeOffers.clock_shape :
    ∀ {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
      {current future : Finset BareMessage},
      TypeOffers env source label target current future →
      env = TypeEnvironment.tock →
      label = TypeLabel.tock ∧ current = ∅ ∧ future = ∅ := by
  intro env source target label current future hOffers
  induction hOffers with
  | action _ _ msg dir hPrem =>
      intro hEnv
      rw [hEnv] at hPrem
      exact absurd hPrem.2 (by simp [TypeEnvironment.hasNeed, TypeEnvironment.tock])
  | action_wait _ _ _ _ hPrem =>
      intro hEnv
      rw [hEnv] at hPrem
      exact absurd hPrem.2.2 (by simp [TypeEnvironment.tock])
  | choice_left _ _ _ _ hPrem | choice_right _ _ _ _ hPrem =>
      intro hEnv
      rw [hEnv] at hPrem
      exact absurd hPrem.2 (by simp [TypeEnvironment.tock])
  | fair_left _ _ _ _ _ hPrem | fair_right _ _ _ _ _ hPrem =>
      intro hEnv
      rw [hEnv] at hPrem
      exact absurd hPrem.2 (by simp [TypeEnvironment.tock])
  | cycle _ _ _ => intro _; exact ⟨rfl, rfl, rfl⟩
  | cycle_wait _ _ hPrem | skip _ _ hPrem | progress _ _ _ hPrem
  | recur _ _ _ _ hPrem =>
      intro hEnv
      rw [hEnv] at hPrem
      exact absurd hPrem.2 (by simp [TypeEnvironment.tock])
  | seq _ _ _ _ _ _ _ _ _ _ hTock ih =>
      intro hEnv; exact absurd (ih hEnv).1 hTock
  | seq_tock _ _ _ _ _ _ _ _ _ _ => intro _; exact ⟨rfl, rfl, rfl⟩
  | seq_fuse _ _ _ _ _ _ _ _ _ hTock ih =>
      intro hEnv; exact absurd (ih hEnv).1 hTock
  | seq_fuse_tock _ _ _ _ _ _ _ _ _ => intro _; exact ⟨rfl, rfl, rfl⟩
  | xoffer_branch _ _ _ _ action _ hPrem =>
      intro hEnv
      rw [hEnv] at hPrem
      exact absurd hPrem.2.2.1
        (by simp [TypeBranchEnabled, TypeEnvironment.tock])
  | xoffer_else _ _ _ _ hPrem | offer_else _ _ _ _ hPrem
  | offer_wait _ _ _ _ hPrem =>
      intro hEnv
      rw [hEnv] at hPrem
      exact absurd hPrem.2.1 (by simp [TypeEnvironment.tock])
  | xoffer_wait _ _ _ _ hPrem =>
      intro hEnv
      rw [hEnv] at hPrem
      exact absurd hPrem.2.2 (by simp [TypeEnvironment.tock])
  | offer_some _ _ _ _ enabled hPrem =>
      intro hEnv
      rw [hEnv] at hPrem
      exact absurd hPrem.2.2 (by simp [TypeBranchEnabled, TypeEnvironment.tock])
  | par _ _ _ interface _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocalLeft hLocalRight _
      ihLeft ihRight =>
      intro hEnv
      obtain ⟨hLeftLabel, hLeftCurrent, hLeftFuture⟩ :=
        ihLeft (hLocalLeft.tock_of_clock (by rw [hEnv]; rfl))
      obtain ⟨hRightLabel, hRightCurrent, hRightFuture⟩ :=
        ihRight (hLocalRight.tock_of_clock (by rw [hEnv]; rfl))
      subst hLeftLabel; subst hRightLabel; subst hLeftCurrent; subst hRightCurrent
      subst hLeftFuture; subst hRightFuture
      refine ⟨?_, ?_, ?_⟩
      · rw [TypeLabel.combine]
      · simp [hideTypeOffers]
      · rw [TypeLabel.combine, if_pos rfl]
  | par_fuse _ _ _ interface _ _ _ _ _ _ _ _ _ _ _ hLocalLeft hLocalRight _
      hNotTock ihLeft ihRight =>
      intro hEnv
      obtain ⟨hLeftLabel, -, -⟩ :=
        ihLeft (hLocalLeft.tock_of_clock (by rw [hEnv]; rfl))
      obtain ⟨hRightLabel, -, -⟩ :=
        ihRight (hLocalRight.tock_of_clock (by rw [hEnv]; rfl))
      subst hLeftLabel; subst hRightLabel
      exact absurd rfl hNotTock
  | par_fuse_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTock _ _ =>
      intro _; exact ⟨hTock, rfl, rfl⟩
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocalLeft _ _ _ ihLeft _ =>
      intro hEnv
      exact absurd (ihLeft (hLocalLeft.tock_of_clock (by rw [hEnv]; rfl))).1
        (by simp [TypeLabel.silent])
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocalRight _ _
      ihRight _ =>
      intro hEnv
      exact absurd (ihRight (hLocalRight.tock_of_clock (by rw [hEnv]; rfl))).1
        (by simp [TypeLabel.silent])

/-! ## Clock-step reflection -/

theorem environmentTock_wellFormed (alphabet : PactTypeAlphabet) :
    Environment.tock.WellFormed alphabet := by
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by simp [Environment.tock]), ?_, ?_⟩ <;>
    simp [Environment.tock, Environment.bareImmediate]

theorem localOfferEnvironment_tock (outer : Environment) (interface : Interface)
    (localProc : Proc) (current : Finset Offer) (future : Finset BareMessage)
    (hClock : outer.clock = true) :
    LocalOfferEnvironment outer interface localProc Environment.tock current
      future Environment.tock :=
  LocalOfferEnvironment.clock _ _ _ _ _ hClock

theorem sync_tock (interface : Interface) :
    Label.Sync interface Label.tock Label.tock := by
  refine ⟨rfl, rfl, Iff.rfl⟩

theorem par_lift_tock {interface : Interface} {alphabet : PactTypeAlphabet}
    {left right leftTarget rightTarget : Proc}
    (hLeftWF : Proc.AlphabetWellFormed left)
    (hRightWF : Proc.AlphabetWellFormed right)
    (hLeft : Offers Environment.tock left Label.tock leftTarget ∅ ∅)
    (hRight : Offers Environment.tock right Label.tock rightTarget ∅ ∅) :
    ∃ target, Offers Environment.tock (Proc.par alphabet left right interface)
      Label.tock target ∅ ∅ := by
  have hLocalLeft := localOfferEnvironment_tock Environment.tock interface left ∅ ∅ rfl
  have hLocalRight := localOfferEnvironment_tock Environment.tock interface right ∅ ∅ rfl
  have hCombine : Label.combine interface Label.tock Label.tock = Label.tock := rfl
  have hLeftAlpha := hLeft.preserves_alphabet hLeftWF
  have hRightAlpha := hRight.preserves_alphabet hRightWF
  by_cases hBoth : leftTarget = Proc.skip left.alphabet ∧
      rightTarget = Proc.skip right.alphabet
  · obtain ⟨hLeftEq, hRightEq⟩ := hBoth
    subst hLeftEq; subst hRightEq
    exact ⟨_, Offers.par_fuse_tock Environment.tock Environment.tock
      Environment.tock interface alphabet left right Label.tock Label.tock ∅ ∅ ∅ ∅
      hLeft hRight hLocalLeft hLocalRight
      ⟨environmentTock_wellFormed alphabet, sync_tock interface⟩ hCombine⟩
  · have hLeftNotSkip : left ≠ Proc.skip left.alphabet := by
      intro hAbsurd
      obtain ⟨hLabel, -, -, -, hClock⟩ :=
        Offers.skip_inversion (by rw [← hAbsurd]; exact hLeft)
      exact absurd hLabel.symm (by simp [Label.silent])
    have hRightNotSkip : right ≠ Proc.skip right.alphabet := by
      intro hAbsurd
      obtain ⟨hLabel, -, -, -, hClock⟩ :=
        Offers.skip_inversion (by rw [← hAbsurd]; exact hRight)
      exact absurd hLabel.symm (by simp [Label.silent])
    have hNotBoth : ¬ (leftTarget = Proc.skip leftTarget.alphabet ∧
        rightTarget = Proc.skip rightTarget.alphabet) := by
      rintro ⟨hLeftEq, hRightEq⟩
      rw [hLeftAlpha] at hLeftEq
      rw [hRightAlpha] at hRightEq
      exact hBoth ⟨hLeftEq, hRightEq⟩
    have hStep := Offers.par Environment.tock Environment.tock Environment.tock
      interface alphabet left leftTarget right rightTarget Label.tock Label.tock
      ∅ ∅ ∅ ∅ hLeftNotSkip hRightNotSkip hLeft hRight hNotBoth hLocalLeft
      hLocalRight ⟨environmentTock_wellFormed alphabet, sync_tock interface⟩
    rw [hCombine, if_pos rfl] at hStep
    simp only [Finset.union_self, hideOfferSet, Finset.filter_empty] at hStep
    exact ⟨_, hStep⟩

/-- Clock-step reflection: a clock step of the abstraction is realised by a
clock step of the process, both with the empty offer pair. -/
theorem clock_step_reflection :
    ∀ {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
      {current future : Finset BareMessage},
      TypeOffers env source label target current future →
      env = TypeEnvironment.tock →
      ∀ process : Proc, inferProcess process = source →
        Proc.AlphabetWellFormed process →
        ∃ processTarget,
          Offers Environment.tock process Label.tock processTarget ∅ ∅ := by
  intro env source target label current future hOffers
  induction hOffers with
  | action _ _ _ _ _ | action_wait _ _ _ _ _ =>
      intro _ process hShape _
      exact (inferProcess_eq_message hShape).elim
  | choice_left _ _ _ _ hPrem | choice_right _ _ _ _ hPrem
  | fair_left _ _ _ _ _ hPrem | fair_right _ _ _ _ _ hPrem
  | cycle_wait _ _ hPrem | skip _ _ hPrem | progress _ _ _ hPrem
  | recur _ _ _ _ hPrem =>
      intro hEnv _ _ _
      rw [hEnv] at hPrem
      exact absurd hPrem.2 (by simp [TypeEnvironment.tock])
  | xoffer_else _ _ _ _ hPrem | offer_else _ _ _ _ hPrem
  | offer_wait _ _ _ _ hPrem =>
      intro hEnv _ _ _
      rw [hEnv] at hPrem
      exact absurd hPrem.2.1 (by simp [TypeEnvironment.tock])
  | xoffer_wait _ _ _ _ hPrem =>
      intro hEnv _ _ _
      rw [hEnv] at hPrem
      exact absurd hPrem.2.2 (by simp [TypeEnvironment.tock])
  | xoffer_branch _ _ _ _ _ _ hPrem =>
      intro hEnv _ _ _
      rw [hEnv] at hPrem
      exact absurd hPrem.2.2.1
        (by simp [TypeBranchEnabled, TypeEnvironment.tock])
  | offer_some _ _ _ _ _ hPrem =>
      intro hEnv _ _ _
      rw [hEnv] at hPrem
      exact absurd hPrem.2.2 (by simp [TypeBranchEnabled, TypeEnvironment.tock])
  | cycle _ alphabet hPrem =>
      intro hEnv process hShape _
      rw [inferProcess_eq_tock hShape]
      exact ⟨Proc.skip alphabet,
        Offers.cycle Environment.tock alphabet
          ⟨environmentTock_wellFormed alphabet, rfl⟩⟩
  | seq _ _ _ _ _ _ _ _ hLeft _ hTock _ =>
      intro hEnv _ _ _
      exact absurd (hLeft.clock_shape hEnv).1 hTock
  | seq_fuse _ _ _ _ _ _ _ _ hLeft hTock _ =>
      intro hEnv _ _ _
      exact absurd (hLeft.clock_shape hEnv).1 hTock
  | seq_tock _ alphabet left left' right _ _ hLeft hSkip ih =>
      intro hEnv process hShape hAlpha
      rcases inferProcess_eq_seq hShape with
        ⟨m, expr, p, rfl, rfl, rfl⟩ | ⟨m, varName, p, rfl, rfl, rfl⟩ |
          ⟨varName, expr, p, rfl, rfl, rfl⟩ | ⟨p₁, p₂, rfl, rfl, rfl⟩
      · cases hLeft
      · cases hLeft
      · cases hLeft
      · rw [Proc.AlphabetWellFormed] at hAlpha
        obtain ⟨t₁, hStep⟩ := ih hEnv p₁ rfl hAlpha.2.2.2.1
        by_cases hSkipTarget : t₁ = Proc.skip t₁.alphabet
        · rw [hSkipTarget] at hStep
          exact ⟨p₂, Offers.seq_fuse_tock Environment.tock alphabet t₁.alphabet
            p₁ p₂ ∅ ∅ hStep⟩
        · exact ⟨Proc.seq alphabet t₁ p₂, Offers.seq_tock Environment.tock alphabet
            p₁ t₁ p₂ ∅ ∅ hStep hSkipTarget⟩
  | seq_fuse_tock _ alphabet skipAlphabet left right _ _ hLeft ih =>
      intro hEnv process hShape hAlpha
      rcases inferProcess_eq_seq hShape with
        ⟨m, expr, p, rfl, rfl, rfl⟩ | ⟨m, varName, p, rfl, rfl, rfl⟩ |
          ⟨varName, expr, p, rfl, rfl, rfl⟩ | ⟨p₁, p₂, rfl, rfl, rfl⟩
      · cases hLeft
      · cases hLeft
      · cases hLeft
      · rw [Proc.AlphabetWellFormed] at hAlpha
        obtain ⟨t₁, hStep⟩ := ih hEnv p₁ rfl hAlpha.2.2.2.1
        by_cases hSkipTarget : t₁ = Proc.skip t₁.alphabet
        · rw [hSkipTarget] at hStep
          exact ⟨p₂, Offers.seq_fuse_tock Environment.tock alphabet t₁.alphabet
            p₁ p₂ ∅ ∅ hStep⟩
        · exact ⟨Proc.seq alphabet t₁ p₂, Offers.seq_tock Environment.tock alphabet
            p₁ t₁ p₂ ∅ ∅ hStep hSkipTarget⟩
  | par _ _ _ interface alphabet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocalLeft
      hLocalRight _ ihLeft ihRight =>
      intro hEnv process hShape hAlpha
      obtain ⟨p₁, p₂, rfl, rfl, rfl⟩ := inferProcess_eq_par hShape
      rw [Proc.AlphabetWellFormed] at hAlpha
      obtain ⟨t₁, hStep₁⟩ :=
        ihLeft (hLocalLeft.tock_of_clock (by rw [hEnv]; rfl)) p₁ rfl hAlpha.2.2.1
      obtain ⟨t₂, hStep₂⟩ :=
        ihRight (hLocalRight.tock_of_clock (by rw [hEnv]; rfl)) p₂ rfl hAlpha.2.2.2
      exact par_lift_tock hAlpha.2.2.1 hAlpha.2.2.2 hStep₁ hStep₂
  | par_fuse _ _ _ interface _ _ _ _ _ _ _ _ _ hLeft hRight hLocalLeft
      hLocalRight _ hNotTock _ _ =>
      intro hEnv _ _ _
      exact absurd (by
        rw [(hLeft.clock_shape (hLocalLeft.tock_of_clock (by rw [hEnv]; rfl))).1,
          (hRight.clock_shape (hLocalRight.tock_of_clock (by rw [hEnv]; rfl))).1]
        rfl) hNotTock
  | par_fuse_tock _ _ _ interface alphabet _ _ _ _ _ _ _ _ _ _ hLocalLeft
      hLocalRight _ _ ihLeft ihRight =>
      intro hEnv process hShape hAlpha
      obtain ⟨p₁, p₂, rfl, rfl, rfl⟩ := inferProcess_eq_par hShape
      rw [Proc.AlphabetWellFormed] at hAlpha
      obtain ⟨t₁, hStep₁⟩ :=
        ihLeft (hLocalLeft.tock_of_clock (by rw [hEnv]; rfl)) p₁ rfl hAlpha.2.2.1
      obtain ⟨t₂, hStep₂⟩ :=
        ihRight (hLocalRight.tock_of_clock (by rw [hEnv]; rfl)) p₂ rfl hAlpha.2.2.2
      exact par_lift_tock hAlpha.2.2.1 hAlpha.2.2.2 hStep₁ hStep₂
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLeft _ _ hLocalLeft _ _ _ _ _ =>
      intro hEnv _ _ _
      exact absurd (hLeft.clock_shape
        (hLocalLeft.tock_of_clock (by rw [hEnv]; rfl))).1 (by simp [TypeLabel.silent])
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRight _ _ _ hLocalRight _ _ _ _ =>
      intro hEnv _ _ _
      exact absurd (hRight.clock_shape
        (hLocalRight.tock_of_clock (by rw [hEnv]; rfl))).1 (by simp [TypeLabel.silent])

/-! ## Admissibility of the recorded environment -/

theorem TypeOffers.env_wellFormed :
    ∀ {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
      {current future : Finset BareMessage},
      TypeOffers env source label target current future →
      source.AlphabetWellFormed → env.WellFormed source.alphabet := by
  intro env source target label current future hOffers
  induction hOffers with
  | action _ _ _ _ hPrem | action_wait _ _ _ _ hPrem
  | choice_left _ _ _ _ hPrem | choice_right _ _ _ _ hPrem
  | fair_left _ _ _ _ _ hPrem | fair_right _ _ _ _ _ hPrem
  | cycle _ _ hPrem | cycle_wait _ _ hPrem | skip _ _ hPrem
  | progress _ _ _ hPrem | recur _ _ _ _ hPrem
  | xoffer_branch _ _ _ _ _ _ hPrem | xoffer_else _ _ _ _ hPrem
  | xoffer_wait _ _ _ _ hPrem | offer_some _ _ _ _ _ hPrem
  | offer_else _ _ _ _ hPrem | offer_wait _ _ _ _ hPrem =>
      intro _; exact hPrem.1
  | seq _ alphabet left _ right _ _ _ _ _ _ ih
  | seq_tock _ alphabet left _ right _ _ _ _ ih =>
      intro hWF
      rw [PactType.AlphabetWellFormed] at hWF
      have := ih hWF.2.2.2.1
      rw [hWF.2.1] at this
      exact this
  | seq_fuse _ alphabet _ left right _ _ _ _ _ ih
  | seq_fuse_tock _ alphabet _ left right _ _ _ ih =>
      intro hWF
      rw [PactType.AlphabetWellFormed] at hWF
      have := ih hWF.2.2.2.1
      rw [hWF.2.1] at this
      exact this
  | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEnv _ _ =>
      intro _; exact hEnv.1
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEnv _ _ _ =>
      intro _; exact hEnv.1
  | par_fuse_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEnv _ _ _ =>
      intro _; exact hEnv.1
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hOuterWF _ _ _ =>
      intro _; exact hOuterWF
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hOuterWF _ _ _ =>
      intro _; exact hOuterWF

theorem environment_eq_tock {env : Environment} {alphabet : PactTypeAlphabet}
    (hWF : env.WellFormed alphabet) (hClock : env.clock = true) :
    env = Environment.tock := by
  obtain ⟨hImmediate, hFuture⟩ := hWF.1 hClock
  cases env with
  | mk immediate future clock =>
      simp only at hImmediate hFuture hClock
      subst hImmediate; subst hFuture; subst hClock
      rfl

end

end Pact
