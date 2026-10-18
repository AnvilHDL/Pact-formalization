import Anvilpp.PactTypes.Proofs.Syntax.TypeTransitionSystemLemmas
import Anvilpp.ProofHelpers.Inference.ConjunctiveCommitment
import Anvilpp.ProofHelpers.Inference.DataPreservation

/-!
# One-step abstraction

`E_P ⊢ P →^α P'` implies `Erase(E_P) ⊢ abs(P) →^{Erase(α)} abs(P')`, and every
decoration of the process step erases to a decoration of the type step.

The conjunctive-commitment clause reads the two premises the paper carries on a
conjunctive offer's branch set: `conjunctCompatible` and `ConjMsgOwn`.
-/

namespace Pact

noncomputable section

open Classical

/-! ## Small facts used by the induction -/

theorem inferBranch_mem {branch : ChoiceBranch} :
    ∀ {branches : List ChoiceBranch}, branch ∈ branches →
      inferBranch branch ∈ inferBranches branches := by
  intro branches
  induction branches with
  | nil => intro hMem; exact absurd hMem (by simp)
  | cons head rest ih =>
      intro hMem
      rw [inferBranches_cons]
      rcases List.mem_cons.1 hMem with rfl | hTail
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hTail)

theorem sdiff_union_sdiff (left right removed : Finset BareMessage) :
    ((left \ removed) ∪ right) \ removed = (left ∪ right) \ removed := by
  ext action
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

@[simp] theorem image_bare_empty :
    (∅ : Finset Offer).image Offer.bare = ∅ := by simp

@[simp] theorem image_bare_send (msg : MessageId) (value : Bool) :
    ({Offer.send msg value} : Finset Offer).image Offer.bare =
      {(msg, MessageDir.send)} := by
  simp [Offer.bare]

@[simp] theorem image_bare_recv (msg : MessageId) :
    ({Offer.recv msg} : Finset Offer).image Offer.bare =
      {(msg, MessageDir.recv)} := by
  simp [Offer.bare]

theorem typeLabel_message_ne_tock (msg : MessageId) (dir : MessageDir) :
    TypeLabel.message msg dir ≠ TypeLabel.tock := by
  simp [TypeLabel.message]

theorem typeLabel_silent_ne_tock : TypeLabel.silent ≠ TypeLabel.tock := by
  simp [TypeLabel.silent]

theorem skip_of_inferProcess_eq_skip (process : Proc)
    (h : inferProcess process = .skip (inferProcess process).alphabet) :
    process = Proc.skip process.alphabet := by
  rw [alphabet_inferProcess] at h
  exact (inferProcess_eq_skip_iff process process.alphabet).1 h

/-! ## Helper Lemma H1 -/

theorem erasure_preserves_offers
    {env : Environment} {process target : Proc} {label : Label}
    {current : Finset Offer} {future : Finset BareMessage}
    (hOffers : Offers env process label target current future)
    (hAlpha : Proc.AlphabetWellFormed process)
    (hConj : Proc.ConjunctRegular process) :
    TypeOffers (eraseEnvironment env) (inferProcess process) (eraseLabel label)
      (inferProcess target) (current.image Offer.bare) future := by
  induction hOffers with
  | send env alphabet msg expr p value hPrem =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      have hLeft : TypeOffers (eraseEnvironment env)
          (.message alphabet msg MessageDir.send)
          (TypeLabel.message msg MessageDir.send) (.skip alphabet)
          ({(msg, MessageDir.send)} ∩ alphabet.actions) (typeFutureOffers (.skip alphabet)) :=
        TypeOffers.action _ _ _ _
          ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1,
            (hasNeed_send_iff env msg).2 hPrem.2.1⟩
      have hFuture :
          ((typeFutureOffers (PactType.skip alphabet) ∪
              sequenceRightMenu (.message alphabet msg MessageDir.send)
                (inferProcess p)) \ ({(msg, MessageDir.send)} ∩ alphabet.actions)) =
            procFutureOffers p \ ({(msg, MessageDir.send)} ∩ alphabet.actions) := by
        simp only [typeFutureOffers_skip, Finset.empty_union, sequenceRightMenu,
          canCompleteDeclared_message, ↓reduceIte,
          procFutureOffers_inferProcess]
      rw [inferProcess, eraseLabel_message, projectCurrent_image, image_bare_send, ← hFuture]
      exact TypeOffers.seq_fuse _ _ _ _ _ _ _ _ hLeft
        (typeLabel_message_ne_tock _ _)
  | send_wait env alphabet msg expr p value hPrem =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      have hLeft : TypeOffers (eraseEnvironment env)
          (.message alphabet msg MessageDir.send) TypeLabel.silent
          (.message alphabet msg MessageDir.send) ({(msg, MessageDir.send)} ∩ alphabet.actions)
          (typeFutureOffers (.message alphabet msg MessageDir.send) \
            ({(msg, MessageDir.send)} ∩ alphabet.actions)) :=
        TypeOffers.action_wait _ _ _ _
          ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1,
            fun h => hPrem.2.1 ((hasNeed_send_iff env msg).1 h), hPrem.2.2.1⟩
      have hFuture :
          (((typeFutureOffers (.message alphabet msg MessageDir.send) \
                ({(msg, MessageDir.send)} ∩ alphabet.actions)) ∪
              sequenceRightMenu (.message alphabet msg MessageDir.send)
                (inferProcess p)) \ ({(msg, MessageDir.send)} ∩ alphabet.actions)) =
            procFutureOffers (Proc.send alphabet msg expr p) \
              ({(msg, MessageDir.send)} ∩ alphabet.actions) := by
        rw [sdiff_union_sdiff, procFutureOffers_inferProcess, inferProcess,
          typeFutureOffers_sequence]
        simp only [canCompleteDeclared_message, ↓reduceIte,
          sequenceRightMenu]
      rw [inferProcess, eraseLabel_silent, projectCurrent_image, image_bare_send, ← hFuture]
      exact TypeOffers.seq _ _ _ _ _ _ _ _ hLeft (by simp) typeLabel_silent_ne_tock
  | recv env alphabet msg varName p value hPrem =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      have hLeft : TypeOffers (eraseEnvironment env)
          (.message alphabet msg MessageDir.recv)
          (TypeLabel.message msg MessageDir.recv) (.skip alphabet)
          ({(msg, MessageDir.recv)} ∩ alphabet.actions) (typeFutureOffers (.skip alphabet)) :=
        TypeOffers.action _ _ _ _
          ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1,
            (hasNeed_recv_iff env msg).2 ⟨value, hPrem.2⟩⟩
      have hFuture :
          ((typeFutureOffers (PactType.skip alphabet) ∪
              sequenceRightMenu (.message alphabet msg MessageDir.recv)
                (inferProcess p)) \ ({(msg, MessageDir.recv)} ∩ alphabet.actions)) =
            procFutureOffers (Semantics.procExprReplace p varName value) \
              ({(msg, MessageDir.recv)} ∩ alphabet.actions) := by
        simp only [typeFutureOffers_skip, Finset.empty_union, sequenceRightMenu,
          canCompleteDeclared_message, ↓reduceIte,
          procFutureOffers_inferProcess,
          inferProcess_procExprReplace]
      rw [inferProcess, eraseLabel_message, projectCurrent_image, image_bare_recv, ← hFuture,
        inferProcess_procExprReplace]
      exact TypeOffers.seq_fuse _ _ _ _ _ _ _ _ hLeft
        (typeLabel_message_ne_tock _ _)
  | recv_wait env alphabet msg varName p hPrem =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      have hLeft : TypeOffers (eraseEnvironment env)
          (.message alphabet msg MessageDir.recv) TypeLabel.silent
          (.message alphabet msg MessageDir.recv) ({(msg, MessageDir.recv)} ∩ alphabet.actions)
          (typeFutureOffers (.message alphabet msg MessageDir.recv) \
            ({(msg, MessageDir.recv)} ∩ alphabet.actions)) :=
        TypeOffers.action_wait _ _ _ _
          ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1,
            fun h => by
              obtain ⟨value, hValue⟩ := (hasNeed_recv_iff env msg).1 h
              exact hPrem.2.1 value hValue,
            hPrem.2.2⟩
      have hFuture :
          (((typeFutureOffers (.message alphabet msg MessageDir.recv) \
                ({(msg, MessageDir.recv)} ∩ alphabet.actions)) ∪
              sequenceRightMenu (.message alphabet msg MessageDir.recv)
                (inferProcess p)) \ ({(msg, MessageDir.recv)} ∩ alphabet.actions)) =
            procFutureOffers (Proc.recv alphabet msg varName p) \
              ({(msg, MessageDir.recv)} ∩ alphabet.actions) := by
        rw [sdiff_union_sdiff, procFutureOffers_inferProcess, inferProcess,
          typeFutureOffers_sequence]
        simp only [canCompleteDeclared_message, ↓reduceIte,
          sequenceRightMenu]
      rw [inferProcess, eraseLabel_silent, projectCurrent_image, image_bare_recv, ← hFuture]
      exact TypeOffers.seq _ _ _ _ _ _ _ _ hLeft (by simp) typeLabel_silent_ne_tock
  | cycle env alphabet hPrem =>
      rw [inferProcess, inferProcess, eraseLabel_tock, image_bare_empty]
      exact TypeOffers.cycle _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2⟩
  | cycle_wait env alphabet hPrem =>
      rw [inferProcess, eraseLabel_silent, image_bare_empty,
        procFutureOffers_inferProcess, inferProcess]
      exact TypeOffers.cycle_wait _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2⟩
  | skip env alphabet hPrem =>
      rw [inferProcess, eraseLabel_silent, image_bare_empty,
        procFutureOffers_inferProcess, inferProcess]
      exact TypeOffers.skip _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2⟩
  | progress env alphabet pid hPrem =>
      rw [inferProcess, inferProcess, eraseLabel_progress, image_bare_empty,
        procFutureOffers_inferProcess, inferProcess]
      exact TypeOffers.progress _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2⟩
  | letp env alphabet varName expr p value hPrem =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      have hLeft : TypeOffers (eraseEnvironment env) (.skip alphabet)
          TypeLabel.silent (.skip alphabet) ∅
          (typeFutureOffers (.skip alphabet)) :=
        TypeOffers.skip _ _
          ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2.1⟩
      have hFuture :
          ((typeFutureOffers (PactType.skip alphabet) ∪
              sequenceRightMenu (.skip alphabet) (inferProcess p)) \ ∅) =
            procFutureOffers (Semantics.procExprReplace p varName value) := by
        simp only [typeFutureOffers_skip, Finset.empty_union, sequenceRightMenu,
          canCompleteDeclared_skip, if_pos, Finset.sdiff_empty,
          procFutureOffers_inferProcess,
          inferProcess_procExprReplace]
      rw [inferProcess, eraseLabel_silent, image_bare_empty, ← hFuture,
        inferProcess_procExprReplace]
      exact TypeOffers.seq_fuse _ _ _ _ _ _ _ _ hLeft typeLabel_silent_ne_tock
  | if_true env alphabet expr ifTrue ifFalse hPrem =>
      rw [inferProcess, eraseLabel_silent, image_bare_empty,
        procFutureOffers_inferProcess, inferProcess]
      exact TypeOffers.choice_left _ _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2.1⟩
  | if_false env alphabet expr ifTrue ifFalse hPrem =>
      rw [inferProcess, eraseLabel_silent, image_bare_empty,
        procFutureOffers_inferProcess, inferProcess]
      exact TypeOffers.choice_right _ _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2.1⟩
  | fair_true env alphabet bid expr ifTrue ifFalse hPrem =>
      rw [inferProcess, eraseLabel_fair, image_bare_empty,
        procFutureOffers_inferProcess, inferProcess]
      exact TypeOffers.fair_left _ _ _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2.1⟩
  | fair_false env alphabet bid expr ifTrue ifFalse hPrem =>
      rw [inferProcess, eraseLabel_fair, image_bare_empty,
        procFutureOffers_inferProcess, inferProcess]
      exact TypeOffers.fair_right _ _ _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2.1⟩
  | recur env alphabet varName body hPrem =>
      rw [inferProcess, eraseLabel_silent, image_bare_empty,
        procFutureOffers_inferProcess, inferProcess_procReplace, inferProcess]
      exact TypeOffers.recur _ _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2⟩
  | seq env alphabet left left' right label current childFuture hOffers hSkip
      hTock ih =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      rw [inferProcess, inferProcess, procSequenceRightMenu_inferProcess]
      exact TypeOffers.seq _ _ _ _ _ _ _ _ (ih hAlpha.2.2.2.1 hConj.1)
        (inferProcess_ne_skip left' hSkip)
        (fun h => hTock ((eraseLabel_eq_tock_iff label).1 h))
  | seq_tock env alphabet left left' right current childFuture hOffers hSkip ih =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      rw [inferProcess, inferProcess, eraseLabel_tock, image_bare_empty]
      have hLeft := ih hAlpha.2.2.2.1 hConj.1
      rw [eraseLabel_tock] at hLeft
      exact TypeOffers.seq_tock _ _ _ _ _ _ _ hLeft
        (inferProcess_ne_skip left' hSkip)
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hOffers hTock ih =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      have hLeft := ih hAlpha.2.2.2.1 hConj.1
      rw [inferProcess_skip] at hLeft
      rw [inferProcess, procSequenceRightMenu_inferProcess]
      exact TypeOffers.seq_fuse _ _ _ _ _ _ _ _ hLeft
        (fun h => hTock ((eraseLabel_eq_tock_iff label).1 h))
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hOffers ih =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      have hLeft := ih hAlpha.2.2.2.1 hConj.1
      rw [inferProcess_skip, eraseLabel_tock] at hLeft
      rw [inferProcess, eraseLabel_tock, image_bare_empty]
      exact TypeOffers.seq_fuse_tock _ _ _ _ _ _ _ hLeft
  | xoffer_send env alphabet elseProcess branches msg expr p value hPrem =>
      have hMem : ((msg, MessageDir.send), inferProcess p) ∈
          inferBranches branches := inferBranch_mem hPrem.2.1
      rw [inferProcess, eraseLabel_message, image_bare_send,
        procFutureOffers_inferProcess, inferProcess,
        ← typeBranchActions_inferBranches]
      exact TypeOffers.xoffer_branch _ _ _ _ (msg, MessageDir.send) _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hMem,
          (hasNeed_send_iff env msg).2 hPrem.2.2.1,
          (typeResolved_iff env branches).2 hPrem.2.2.2.2⟩
  | xoffer_recv env alphabet elseProcess branches msg varName p value hPrem =>
      have hMem : ((msg, MessageDir.recv), inferProcess p) ∈
          inferBranches branches := inferBranch_mem hPrem.2.1
      rw [inferProcess, eraseLabel_message, image_bare_recv,
        procFutureOffers_inferProcess, inferProcess,
        ← typeBranchActions_inferBranches, inferProcess_procExprReplace]
      exact TypeOffers.xoffer_branch _ _ _ _ (msg, MessageDir.recv) _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hMem,
          (hasNeed_recv_iff env msg).2 ⟨value, hPrem.2.2.1⟩,
          (typeResolved_iff env branches).2 hPrem.2.2.2⟩
  | xoffer_else env alphabet elseProcess branches hPrem =>
      rw [inferProcess, eraseLabel_silent, projectCurrent_image, branchOfferSet_image,
        procFutureOffers_inferProcess, inferProcess,
        ← typeBranchActions_inferBranches]
      exact TypeOffers.xoffer_else _ _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2.1,
          (typeNoImmediateBranch_iff env branches).2 hPrem.2.2.1,
          (typeResolved_iff env branches).2 hPrem.2.2.2⟩
  | xoffer_wait env alphabet elseProcess branches hPrem =>
      rw [inferProcess, eraseLabel_silent, waitingOfferSet_image,
        ← typeWaitingOffers_eq env branches, procFutureOffers_inferProcess,
        inferProcess]
      exact TypeOffers.xoffer_wait _ _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1,
          fun h => hPrem.2.1 ((typeResolved_iff env branches).1 h), hPrem.2.2⟩
  | offer_some env alphabet elseProcess branches enabled hPrem =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      have hCommit := inferProcess_parallelProcessBranchesSelecting
        hAlpha.2.2.2 hConj.1 hPrem.2.1
      rw [inferProcess, eraseLabel_silent, image_bare_empty,
        procFutureOffers_inferProcess, hCommit]
      exact TypeOffers.offer_some _ _ _ _ (inferBranch enabled)
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1,
          inferBranch_mem hPrem.2.1,
          (typeBranchEnabled_iff env enabled).2 hPrem.2.2⟩
  | offer_else env alphabet elseProcess branches hPrem =>
      rw [inferProcess, eraseLabel_silent, projectCurrent_image, branchOfferSet_image,
        procFutureOffers_inferProcess, ← typeBranchActions_inferBranches]
      exact TypeOffers.offer_else _ _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2.1,
          (typeNoImmediateBranch_iff env branches).2 hPrem.2.2.1,
          (typeResolved_iff env branches).2 hPrem.2.2.2⟩
  | offer_wait env alphabet elseProcess branches hPrem =>
      rw [inferProcess, eraseLabel_silent, projectCurrent_image, branchOfferSet_image,
        procFutureOffers_inferProcess, inferProcess,
        ← typeBranchActions_inferBranches]
      exact TypeOffers.offer_wait _ _ _ _
        ⟨(environment_wellFormed_iff env alphabet).1 hPrem.1, hPrem.2.1,
          (typeNoImmediateBranch_iff env branches).2 hPrem.2.2.1,
          fun h => hPrem.2.2.2 ((typeResolved_iff env branches).1 h)⟩
  | par outer leftEnv rightEnv interface alphabet left left' right right'
      leftLabel rightLabel leftCurrent rightCurrent leftFuture rightFuture
      hLeftSkip hRightSkip hLeftOffers hRightOffers hNotBoth hLocalLeft
      hLocalRight hEnv ihLeft ihRight =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      have hCurrent : (hideOfferSet interface (leftCurrent ∪ rightCurrent)).image
            Offer.bare =
          hideTypeOffers interface
            (leftCurrent.image Offer.bare ∪ rightCurrent.image Offer.bare) := by
        rw [image_hideOfferSet, Finset.image_union]
      have hFuture :
          (if Label.combine interface leftLabel rightLabel = Label.tock then
              (∅ : Finset BareMessage)
            else hideProcOffers interface (leftFuture ∪ rightFuture)) =
            (if TypeLabel.combine interface (eraseLabel leftLabel)
                  (eraseLabel rightLabel) = TypeLabel.tock then ∅
              else hideTypeOffers interface (leftFuture ∪ rightFuture)) := by
        by_cases hTock : Label.combine interface leftLabel rightLabel = Label.tock
        · rw [if_pos hTock, if_pos (by rw [← eraseLabel_combine, hTock]; rfl)]
        · rw [if_neg hTock, if_neg (fun hAbsurd => hTock
            ((eraseLabel_eq_tock_iff _).1 (by rw [eraseLabel_combine]; exact hAbsurd))),
            hideProcOffers_eq]
      rw [inferProcess, inferProcess, eraseLabel_combine, hCurrent, hFuture]
      exact TypeOffers.par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (inferProcess_ne_skip left hLeftSkip) (inferProcess_ne_skip right hRightSkip)
        (ihLeft hAlpha.2.2.1 hConj.1) (ihRight hAlpha.2.2.2 hConj.2)
        (fun h => hNotBoth ⟨skip_of_inferProcess_eq_skip left' h.1,
          skip_of_inferProcess_eq_skip right' h.2⟩)
        (localTypeOfferEnvironment_erase hLocalLeft)
        (localTypeOfferEnvironment_erase hLocalRight)
        ⟨(environment_wellFormed_iff outer alphabet).1 hEnv.1,
          (typeSync_eraseLabel interface leftLabel rightLabel).2 hEnv.2⟩
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent rightCurrent leftFuture rightFuture hLeftOffers
      hRightOffers hLocalLeft hLocalRight hEnv hNotTock ihLeft ihRight =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      have hLeft := ihLeft hAlpha.2.2.1 hConj.1
      have hRight := ihRight hAlpha.2.2.2 hConj.2
      rw [inferProcess_skip, ← alphabet_inferProcess left] at hLeft
      rw [inferProcess_skip, ← alphabet_inferProcess right] at hRight
      rw [inferProcess_skip, inferProcess, eraseLabel_combine, image_hideOfferSet,
        Finset.image_union, hideProcOffers_eq]
      exact TypeOffers.par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ hLeft hRight
        (localTypeOfferEnvironment_erase hLocalLeft)
        (localTypeOfferEnvironment_erase hLocalRight)
        ⟨(environment_wellFormed_iff outer alphabet).1 hEnv.1,
          (typeSync_eraseLabel interface leftLabel rightLabel).2 hEnv.2⟩
        (fun hAbsurd => hNotTock
          ((eraseLabel_eq_tock_iff _).1 (by rw [eraseLabel_combine]; exact hAbsurd)))
  | par_fuse_tock outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent rightCurrent leftFuture rightFuture hLeftOffers
      hRightOffers hLocalLeft hLocalRight hEnv hTock ihLeft ihRight =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      have hLeft := ihLeft hAlpha.2.2.1 hConj.1
      have hRight := ihRight hAlpha.2.2.2 hConj.2
      rw [inferProcess_skip, ← alphabet_inferProcess left] at hLeft
      rw [inferProcess_skip, ← alphabet_inferProcess right] at hRight
      rw [inferProcess_skip, inferProcess, eraseLabel_combine, image_bare_empty]
      exact TypeOffers.par_fuse_tock _ _ _ _ _ _ _ _ _ _ _ _ _ hLeft hRight
        (localTypeOfferEnvironment_erase hLocalLeft)
        (localTypeOfferEnvironment_erase hLocalRight)
        ⟨(environment_wellFormed_iff outer alphabet).1 hEnv.1,
          (typeSync_eraseLabel interface leftLabel rightLabel).2 hEnv.2⟩
        (by rw [← eraseLabel_combine, hTock]; rfl)
  | left_complete outer leftEnv rightEnv interface alphabet left right right'
      rightLabel leftCurrent rightCurrent leftFuture rightFuture hLeftIsSkip
      hRightSkip hLeftOffers hRightOffers hRightTargetSkip hLocalLeft
      hLocalRight hOuterWF hSync ihLeft ihRight =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      have hLeft := ihLeft hAlpha.2.2.1 hConj.1
      have hRight := ihRight hAlpha.2.2.2 hConj.2
      rw [eraseLabel_silent] at hLeft
      have hLeftSkipType : inferProcess left = .skip (inferProcess left).alphabet := by
        rw [alphabet_inferProcess]
        exact (inferProcess_eq_skip_iff left left.alphabet).2 hLeftIsSkip
      have hSyncType : TypeLabel.Sync interface TypeLabel.silent
          (eraseLabel rightLabel) := by
        rw [← eraseLabel_silent]
        exact (typeSync_eraseLabel interface Label.silent rightLabel).2 hSync
      rw [inferProcess, inferProcess_reannotate, image_hideOfferSet,
        hideProcOffers_eq]
      exact TypeOffers.left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ hLeftSkipType
        (inferProcess_ne_skip right hRightSkip) hLeft hRight
        (inferProcess_ne_skip right' hRightTargetSkip)
        (localTypeOfferEnvironment_erase hLocalLeft)
        (localTypeOfferEnvironment_erase hLocalRight)
        ((environment_wellFormed_iff outer alphabet).1 hOuterWF) hSyncType
  | right_complete outer leftEnv rightEnv interface alphabet left left' right
      leftLabel leftCurrent rightCurrent leftFuture rightFuture hRightIsSkip
      hLeftSkip hRightOffers hLeftOffers hLeftTargetSkip hLocalLeft
      hLocalRight hOuterWF hSync ihRight ihLeft =>
      rw [Proc.AlphabetWellFormed] at hAlpha
      rw [Proc.ConjunctRegular] at hConj
      have hLeft := ihLeft hAlpha.2.2.1 hConj.1
      have hRight := ihRight hAlpha.2.2.2 hConj.2
      rw [eraseLabel_silent] at hRight
      have hRightSkipType : inferProcess right = .skip (inferProcess right).alphabet := by
        rw [alphabet_inferProcess]
        exact (inferProcess_eq_skip_iff right right.alphabet).2 hRightIsSkip
      have hSyncType : TypeLabel.Sync interface (eraseLabel leftLabel)
          TypeLabel.silent := by
        rw [← eraseLabel_silent]
        exact (typeSync_eraseLabel interface leftLabel Label.silent).2 hSync
      rw [inferProcess, inferProcess_reannotate, image_hideOfferSet,
        hideProcOffers_eq]
      exact TypeOffers.right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ hRightSkipType
        (inferProcess_ne_skip left hLeftSkip) hRight hLeft
        (inferProcess_ne_skip left' hLeftTargetSkip)
        (localTypeOfferEnvironment_erase hLocalLeft)
        (localTypeOfferEnvironment_erase hLocalRight)
        ((environment_wellFormed_iff outer alphabet).1 hOuterWF) hSyncType

/-! ## From a decorated step to the step relation -/

/-- Every decorated type step is a type step. -/
theorem TypeOffers.toTypeTransition
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    TypeTransition env source label target := by
  induction hOffers with
  | action _ _ _ _ hPrem => exact TypeTransition.action _ _ _ _ hPrem
  | action_wait _ _ _ _ hPrem =>
      exact TypeTransition.action_wait _ _ _ _ hPrem
  | choice_left _ _ _ _ hPrem =>
      exact TypeTransition.choice_left _ _ _ _ hPrem.1 hPrem.2
  | choice_right _ _ _ _ hPrem =>
      exact TypeTransition.choice_right _ _ _ _ hPrem.1 hPrem.2
  | fair_left _ _ _ _ _ hPrem =>
      exact TypeTransition.fair_left _ _ _ _ _ hPrem.1 hPrem.2
  | fair_right _ _ _ _ _ hPrem =>
      exact TypeTransition.fair_right _ _ _ _ _ hPrem.1 hPrem.2
  | cycle _ _ hPrem => exact TypeTransition.cycle _ _ hPrem
  | cycle_wait _ _ hPrem => exact TypeTransition.cycle_wait _ _ hPrem
  | skip _ _ hPrem => exact TypeTransition.skip _ _ hPrem
  | progress _ _ _ hPrem => exact TypeTransition.progress _ _ _ hPrem.1 hPrem.2
  | recur _ _ _ _ hPrem => exact TypeTransition.recur _ _ _ _ hPrem.1 hPrem.2
  | seq _ _ _ _ _ _ _ _ _ hSkip _ ih => exact TypeTransition.seq _ _ _ _ _ _ ih hSkip
  | seq_tock _ _ _ _ _ _ _ _ hSkip ih =>
      exact TypeTransition.seq _ _ _ _ _ _ ih hSkip
  | seq_fuse _ _ _ _ _ _ _ _ _ _ ih => exact TypeTransition.seq_fuse _ _ _ _ _ _ ih
  | seq_fuse_tock _ _ _ _ _ _ _ _ ih =>
      exact TypeTransition.seq_fuse _ _ _ _ _ _ ih
  | xoffer_branch _ _ _ _ _ _ hPrem =>
      exact TypeTransition.xoffer_branch _ _ _ _ _ _ hPrem
  | xoffer_else _ _ _ _ hPrem =>
      exact TypeTransition.xoffer_else _ _ _ _ hPrem
  | xoffer_wait _ _ _ _ hPrem =>
      exact TypeTransition.xoffer_wait _ _ _ _ hPrem
  | offer_some _ _ _ _ _ hPrem =>
      exact TypeTransition.offer_some _ _ _ _ _ hPrem
  | offer_else _ _ _ _ hPrem =>
      exact TypeTransition.offer_else _ _ _ _ hPrem
  | offer_wait _ _ _ _ hPrem =>
      exact TypeTransition.offer_wait _ _ _ _ hPrem
  | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLeftSkip hRightSkip hLeftOffers
      hRightOffers hNotBoth hLocalLeft hLocalRight hEnv ihLeft ihRight =>
      exact TypeTransition.par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLeftSkip hRightSkip
        ihLeft hLeftOffers ihRight hRightOffers hNotBoth
        ⟨hEnv.1, hLocalLeft, hLocalRight, hEnv.2⟩
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ hLeftOffers hRightOffers hLocalLeft
      hLocalRight hEnv _ ihLeft ihRight =>
      exact TypeTransition.par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ ihLeft hLeftOffers
        ihRight hRightOffers ⟨hEnv.1, hLocalLeft, hLocalRight, hEnv.2⟩
  | par_fuse_tock _ _ _ _ _ _ _ _ _ _ _ _ _ hLeftOffers hRightOffers hLocalLeft
      hLocalRight hEnv _ ihLeft ihRight =>
      exact TypeTransition.par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ ihLeft hLeftOffers
        ihRight hRightOffers ⟨hEnv.1, hLocalLeft, hLocalRight, hEnv.2⟩
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ hLeftIsSkip hRightSkip hLeftOffers
      hRightOffers hTargetSkip hLocalLeft hLocalRight hOuterWF hSync ihLeft
      ihRight =>
      exact TypeTransition.left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ hLeftIsSkip
        hRightSkip ihLeft hLeftOffers ihRight hRightOffers hTargetSkip
        hLocalLeft hLocalRight hOuterWF hSync
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ hRightIsSkip hLeftSkip hRightOffers
      hLeftOffers hTargetSkip hLocalLeft hLocalRight hOuterWF hSync ihRight
      ihLeft =>
      exact TypeTransition.right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ hRightIsSkip
        hLeftSkip ihRight hRightOffers ihLeft hLeftOffers hTargetSkip
        hLocalLeft hLocalRight hOuterWF hSync

/-! ## Helper Lemma H7 -/

/-- One process step abstracts to one type step. -/
theorem one_step_abstraction
    {env : Environment} {process target : Proc} {label : Label}
    (hAlpha : Proc.AlphabetWellFormed process) (hConj : Proc.ConjunctRegular process)
    (hStep : ProcessTransition env process label target) :
    TypeTransition (eraseEnvironment env) (inferProcess process)
      (eraseLabel label) (inferProcess target) := by
  obtain ⟨current, future, hOffers⟩ := hStep
  exact (erasure_preserves_offers hOffers hAlpha hConj).toTypeTransition

end

end Pact
