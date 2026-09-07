import Anvilpp.ProofHelpers.Inference.AbstractionMenus

/-!
# Erasure and local side conditions

Erasure keeps every side condition an `Off` clause reads: environment
well-formedness, immediate demands, branch resolution, the waiting menu,
label synchronization, and the sibling-local environments.
-/

namespace Pact

noncomputable section

open Classical

/-! ## Environments -/

@[simp] theorem eraseEnvironment_immediate (env : Environment) :
    (eraseEnvironment env).immediate = env.bareImmediate := rfl

@[simp] theorem eraseEnvironment_future (env : Environment) :
    (eraseEnvironment env).future = env.future := rfl

@[simp] theorem eraseEnvironment_clock (env : Environment) :
    (eraseEnvironment env).clock = env.clock := rfl

theorem bareNeed_eq_typeNeed : bareNeed = typeNeed := rfl

/-- `E ∈ Env_P` is unchanged by erasure. -/
theorem environment_wellFormed_iff (env : Environment)
    (alphabet : PactTypeAlphabet) :
    env.WellFormed alphabet ↔ (eraseEnvironment env).WellFormed alphabet := by
  unfold Environment.WellFormed TypeEnvironment.WellFormed
  rw [eraseEnvironment_immediate, eraseEnvironment_future, eraseEnvironment_clock,
    ← bareNeed_eq_typeNeed]
  constructor
  · rintro ⟨hClock, hDisjoint, hImm, hFut⟩
    exact ⟨fun h => ⟨by simp [Environment.bareImmediate, (hClock h).1],
      (hClock h).2⟩, hDisjoint, hImm, hFut⟩
  · rintro ⟨hClock, hDisjoint, hImm, hFut⟩
    refine ⟨fun h => ⟨?_, (hClock h).2⟩, hDisjoint, hImm, hFut⟩
    simpa [Environment.bareImmediate, Finset.image_eq_empty] using (hClock h).1

/-- An immediate receive offer is exactly the erased need of a send. -/
theorem hasNeed_send_iff (env : Environment) (msg : MessageId) :
    (eraseEnvironment env).hasNeed (msg, MessageDir.send) ↔ env.hasRecv msg := by
  simp only [TypeEnvironment.hasNeed, eraseEnvironment_immediate,
    Environment.bareImmediate, Environment.hasRecv, Finset.mem_image,
    MessageDir.invert]
  constructor
  · rintro ⟨offer, hOffer, hEq⟩
    cases offer with
    | send m v => exact absurd hEq (by simp [Offer.bare])
    | recv m =>
        have hm : m = msg := by simpa [Offer.bare] using hEq
        exact hm ▸ hOffer
  · intro h
    exact ⟨Offer.recv msg, h, rfl⟩

/-- An immediate send offer is exactly the erased need of a receive. -/
theorem hasNeed_recv_iff (env : Environment) (msg : MessageId) :
    (eraseEnvironment env).hasNeed (msg, MessageDir.recv) ↔
      ∃ value, env.hasSend msg value := by
  simp only [TypeEnvironment.hasNeed, eraseEnvironment_immediate,
    Environment.bareImmediate, Environment.hasSend, Finset.mem_image,
    MessageDir.invert]
  constructor
  · rintro ⟨offer, hOffer, hEq⟩
    cases offer with
    | send m v =>
        have hm : m = msg := by simpa [Offer.bare] using hEq
        exact ⟨v, hm ▸ hOffer⟩
    | recv m => exact absurd hEq (by simp [Offer.bare])
  · rintro ⟨value, h⟩
    exact ⟨Offer.send msg value, h, rfl⟩

/-! ## Branch side conditions -/

/-- Projection commutes with erasure of concrete offers. -/
theorem projectCurrent_image (alphabet : PactTypeAlphabet) (offers : Finset Offer) :
    (projectCurrent alphabet offers).image Offer.bare =
      offers.image Offer.bare ∩ alphabet.actions := by
  ext action
  simp only [projectCurrent, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨offer, ⟨hOffer, hDeclared⟩, rfl⟩
    exact ⟨⟨offer, hOffer, rfl⟩, hDeclared⟩
  · rintro ⟨⟨offer, hOffer, rfl⟩, hDeclared⟩
    exact ⟨offer, ⟨hOffer, hDeclared⟩, rfl⟩

@[simp] theorem inferBranch_fst (branch : ChoiceBranch) :
    (inferBranch branch).1 = ChoiceBranch.action branch := rfl

theorem bare_choiceBranchOffer (branch : ChoiceBranch) :
    Offer.bare (ChoiceBranch.offer branch) = ChoiceBranch.action branch := by
  cases branch <;>
    rfl

/-- `Act_B` as concrete offers erases to `Act_B`. -/
theorem branchOfferSet_image (branches : List ChoiceBranch) :
    (branchOfferSet branches).image Offer.bare = branchActions branches := by
  ext action
  simp only [branchOfferSet, branchActions, Finset.mem_image, List.mem_toFinset,
    List.mem_map]
  constructor
  · rintro ⟨offer, ⟨branch, hMem, rfl⟩, rfl⟩
    exact ⟨branch, hMem, (bare_choiceBranchOffer branch).symm⟩
  · rintro ⟨branch, hMem, rfl⟩
    exact ⟨ChoiceBranch.offer branch, ⟨branch, hMem, rfl⟩,
      bare_choiceBranchOffer branch⟩

theorem typeResolved_iff (env : Environment) (branches : List ChoiceBranch) :
    TypeResolved (eraseEnvironment env) (inferBranches branches) ↔
      Resolved env branches := by
  unfold TypeResolved Resolved
  rw [typeBranchNeeds_inferBranches, eraseEnvironment_future]

theorem typeNoImmediateBranch_iff (env : Environment)
    (branches : List ChoiceBranch) :
    TypeNoImmediateBranch (eraseEnvironment env) (inferBranches branches) ↔
      NoImmediateBranch env branches := by
  unfold TypeNoImmediateBranch NoImmediateBranch
  rw [typeBranchNeeds_inferBranches, eraseEnvironment_immediate]

theorem typeBranchEnabled_iff (env : Environment) (branch : ChoiceBranch) :
    TypeBranchEnabled (eraseEnvironment env) (inferBranch branch) ↔
      BranchEnabled env branch := by
  unfold TypeBranchEnabled BranchEnabled
  rw [inferBranch_fst, eraseEnvironment_immediate, ← bareNeed_eq_typeNeed]
  rfl

/-- `W(E,B)` is unchanged by erasure. -/
theorem typeWaitingOffers_eq (env : Environment) (branches : List ChoiceBranch) :
    typeWaitingOffers (eraseEnvironment env) (inferBranches branches) =
      waitingOffers env branches := by
  unfold typeWaitingOffers waitingOffers
  rw [typeBranchActions_inferBranches, eraseEnvironment_future,
    ← bareNeed_eq_typeNeed]

/-- The concrete witnesses behind `W(E,B)` erase to `W(E,B)`. -/
theorem waitingOfferSet_image (env : Environment) (branches : List ChoiceBranch) :
    (waitingOfferSet env branches).image Offer.bare = waitingOffers env branches := by
  ext action
  simp only [waitingOfferSet, Finset.mem_image, List.mem_toFinset, List.mem_map,
    List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨offer, ⟨branch, ⟨hMem, hWait⟩, rfl⟩, rfl⟩
    rwa [bare_choiceBranchOffer]
  · intro hAction
    have hMem : action ∈ branchActions branches :=
      (Finset.mem_inter.1 hAction).2
    rw [branchActions, List.mem_toFinset, List.mem_map] at hMem
    obtain ⟨branch, hBranch, hEq⟩ := hMem
    refine ⟨ChoiceBranch.offer branch, ⟨branch, ⟨hBranch, ?_⟩, rfl⟩, ?_⟩
    · rw [hEq]; exact hAction
    · rw [bare_choiceBranchOffer, hEq]

/-! ## Labels -/

@[simp] theorem eraseLabel_silent : eraseLabel Label.silent = TypeLabel.silent := by
  simp [eraseLabel, Label.silent, TypeLabel.silent]

@[simp] theorem eraseLabel_tock : eraseLabel Label.tock = TypeLabel.tock := rfl

@[simp] theorem eraseLabel_message (msg : MessageId) (dir : MessageDir)
    (value : Bool) :
    eraseLabel (Label.message msg dir value) = TypeLabel.message msg dir := by
  simp [eraseLabel, Label.message, TypeLabel.message, eraseObservation]

@[simp] theorem eraseLabel_fair (bid : BranchId) (taken : Bool) :
    eraseLabel (Label.fair bid taken) = TypeLabel.fair bid taken := by
  simp [eraseLabel, Label.fair, TypeLabel.fair, eraseObservation]

@[simp] theorem eraseLabel_progress (pid : ProcId) :
    eraseLabel (Label.progress pid) = TypeLabel.progress pid := by
  simp [eraseLabel, Label.progress, TypeLabel.progress, eraseObservation]

@[simp] theorem eraseLabel_eq_tock_iff (label : Label) :
    eraseLabel label = TypeLabel.tock ↔ label = Label.tock := by
  cases label <;> simp [eraseLabel]

@[simp] theorem isTock_eraseLabel (label : Label) :
    (eraseLabel label).isTock ↔ label.isTock := by
  cases label <;> simp [eraseLabel, Label.isTock, TypeLabel.isTock]

theorem sends_eraseLabel (label : Label) : (eraseLabel label).sends = label.sends := by
  cases label with
  | tock => rfl
  | actions obs =>
      ext msg
      simp only [eraseLabel, TypeLabel.sends, Label.sends, TypeLabel.messageIdsWith,
        Label.messageIdsWith, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨observation, ⟨⟨source, hSource, rfl⟩, hDir⟩, hMsg⟩
        refine ⟨source, ⟨hSource, ?_⟩, ?_⟩
        · cases source <;> simp_all [eraseObservation]
        · cases source <;> simp_all [eraseObservation]
      · rintro ⟨source, ⟨hSource, hDir⟩, hMsg⟩
        refine ⟨eraseObservation source, ⟨⟨source, hSource, rfl⟩, ?_⟩, ?_⟩
        · cases source <;> simp_all [eraseObservation]
        · cases source <;> simp_all [eraseObservation]

theorem recvs_eraseLabel (label : Label) : (eraseLabel label).recvs = label.recvs := by
  cases label with
  | tock => rfl
  | actions obs =>
      ext msg
      simp only [eraseLabel, TypeLabel.recvs, Label.recvs, TypeLabel.messageIdsWith,
        Label.messageIdsWith, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨observation, ⟨⟨source, hSource, rfl⟩, hDir⟩, hMsg⟩
        refine ⟨source, ⟨hSource, ?_⟩, ?_⟩
        · cases source <;> simp_all [eraseObservation]
        · cases source <;> simp_all [eraseObservation]
      · rintro ⟨source, ⟨hSource, hDir⟩, hMsg⟩
        refine ⟨eraseObservation source, ⟨⟨source, hSource, rfl⟩, ?_⟩, ?_⟩
        · cases source <;> simp_all [eraseObservation]
        · cases source <;> simp_all [eraseObservation]

/-- `Sync_I` is unchanged by erasure. -/
theorem typeSync_eraseLabel (interface : Interface) (left right : Label) :
    TypeLabel.Sync interface (eraseLabel left) (eraseLabel right) ↔
      Label.Sync interface left right := by
  unfold TypeLabel.Sync Label.Sync
  rw [sends_eraseLabel, sends_eraseLabel, recvs_eraseLabel, recvs_eraseLabel]
  simp

theorem synced_eraseLabel (interface : Interface) (left right : Label) :
    TypeLabel.synced interface (eraseLabel left) (eraseLabel right) =
      Label.synced interface left right := by
  unfold TypeLabel.synced Label.synced
  rw [sends_eraseLabel, sends_eraseLabel]

/-- `α₁ ∪_I α₂` commutes with erasure. -/
theorem eraseLabel_combine (interface : Interface) (left right : Label) :
    eraseLabel (Label.combine interface left right) =
      TypeLabel.combine interface (eraseLabel left) (eraseLabel right) := by
  cases left with
  | tock =>
      cases right with
      | tock => rfl
      | actions R =>
          simp [Label.combine, TypeLabel.combine, eraseLabel, Label.silent,
            TypeLabel.silent]
  | actions L =>
      cases right with
      | tock =>
          simp [Label.combine, TypeLabel.combine, eraseLabel, Label.silent,
            TypeLabel.silent]
      | actions R =>
          have hS : TypeLabel.synced interface (eraseLabel (Label.actions L))
              (eraseLabel (Label.actions R)) =
              Label.synced interface (Label.actions L) (Label.actions R) :=
            synced_eraseLabel interface (Label.actions L) (Label.actions R)
          simp only [eraseLabel] at hS
          simp only [Label.combine, TypeLabel.combine, eraseLabel, hS,
            Finset.image_union, Finset.image_image]
          congr 1
          congr 1
          ext observation
          constructor
          · intro hMem
            obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.1 hMem
            obtain ⟨hUnion, hRaw⟩ := Finset.mem_filter.1 hSource
            refine Finset.mem_filter.2 ⟨?_, ?_⟩
            · rcases Finset.mem_union.1 hUnion with h | h
              · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
              · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
            · cases source <;>
                simpa [eraseObservation, Label.isRawSyncedMessage,
                  TypeLabel.isRawSyncedMessage] using hRaw
          · intro hMem
            obtain ⟨hUnion, hRaw⟩ := Finset.mem_filter.1 hMem
            rcases Finset.mem_union.1 hUnion with h | h
            · obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.1 h
              exact Finset.mem_image_of_mem _ (Finset.mem_filter.2
                ⟨Finset.mem_union_left _ hSource, by
                  cases source <;>
                    simpa [eraseObservation, Label.isRawSyncedMessage,
                      TypeLabel.isRawSyncedMessage] using hRaw⟩)
            · obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.1 h
              exact Finset.mem_image_of_mem _ (Finset.mem_filter.2
                ⟨Finset.mem_union_right _ hSource, by
                  cases source <;>
                    simpa [eraseObservation, Label.isRawSyncedMessage,
                      TypeLabel.isRawSyncedMessage] using hRaw⟩)

/-! ## Interface restriction and hiding -/

theorem messageId_eq_bare_fst (offer : Offer) :
    offer.messageId = (Offer.bare offer).1 := by
  cases offer <;> rfl

theorem image_restrictCurrent (interface : Interface) (offers : Finset Offer) :
    (restrictCurrent interface offers).image Offer.bare =
      restrictTypeOffers interface (offers.image Offer.bare) := by
  simp only [restrictCurrent, restrictTypeOffers]
  ext action
  constructor
  · intro hMem
    obtain ⟨offer, hOffer, rfl⟩ := Finset.mem_image.1 hMem
    obtain ⟨hSource, hId⟩ := Finset.mem_filter.1 hOffer
    exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hSource,
      by rwa [messageId_eq_bare_fst] at hId⟩
  · intro hMem
    obtain ⟨hSource, hId⟩ := Finset.mem_filter.1 hMem
    obtain ⟨offer, hOffer, rfl⟩ := Finset.mem_image.1 hSource
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2
      ⟨hOffer, by rwa [messageId_eq_bare_fst]⟩)

theorem image_hideOfferSet (interface : Interface) (offers : Finset Offer) :
    (hideOfferSet interface offers).image Offer.bare =
      hideTypeOffers interface (offers.image Offer.bare) := by
  simp only [hideOfferSet, hideTypeOffers]
  ext action
  constructor
  · intro hMem
    obtain ⟨offer, hOffer, rfl⟩ := Finset.mem_image.1 hMem
    obtain ⟨hSource, hId⟩ := Finset.mem_filter.1 hOffer
    exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hSource,
      by rwa [messageId_eq_bare_fst] at hId⟩
  · intro hMem
    obtain ⟨hSource, hId⟩ := Finset.mem_filter.1 hMem
    obtain ⟨offer, hOffer, rfl⟩ := Finset.mem_image.1 hSource
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2
      ⟨hOffer, by rwa [messageId_eq_bare_fst]⟩)

/-! ## Sibling-local environments -/

@[simp] theorem eraseEnvironment_tock :
    eraseEnvironment Environment.tock = TypeEnvironment.tock := by
  simp [eraseEnvironment, Environment.tock, TypeEnvironment.tock,
    Environment.bareImmediate]

/-- The sibling-local environment relation is preserved by erasure. -/
theorem localTypeOfferEnvironment_erase
    {outer siblingEnv localEnv : Environment} {interface : Interface}
    {localProc : Proc} {current : Finset Offer} {future : Finset BareMessage}
    (hLocal : LocalOfferEnvironment outer interface localProc siblingEnv current
      future localEnv) :
    LocalTypeOfferEnvironment (eraseEnvironment outer) interface
      (inferProcess localProc) (eraseEnvironment siblingEnv)
      (current.image Offer.bare) future (eraseEnvironment localEnv) := by
  cases hLocal with
  | clock _ _ _ _ hClock =>
      rw [eraseEnvironment_tock]
      exact .clock _ _ _ _ _ hClock
  | ordinary _ _ _ _ _ _ hOuter hSibling hLocalClock hImmediate hFuture =>
      refine .ordinary _ _ _ _ _ _ _ hOuter hSibling hLocalClock ?_ ?_
      · simp only [eraseEnvironment_immediate, Environment.bareImmediate,
          hImmediate, Finset.image_union, image_restrictCurrent]
      · simp only [eraseEnvironment_future, eraseEnvironment_immediate, hFuture,
          restrictFuture_eq, Environment.bareImmediate]

end

end Pact
