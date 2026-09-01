import Anvilpp.PactTypes.Syntax.TypeErasure

namespace Pact

namespace TypeLabel

/-! ## Membership helpers for `sends`, `recvs` and `synced` -/

/-- A message id is sent by a label exactly when the label carries the send observation. -/
private theorem mem_sends_iff (label : TypeLabel) (msg : MessageId) :
    msg ∈ label.sends ↔ label.contains (.message msg .send) := by
  cases label with
  | tock => simp [sends, contains]
  | actions observations =>
      simp only [sends, messageIdsWith, Finset.mem_image, Finset.mem_filter, contains]
      constructor
      · rintro ⟨observation, ⟨hMem, hDir⟩, hMsg⟩
        cases observation <;> simp_all
      · intro hMem
        exact ⟨.message msg .send, ⟨hMem, rfl⟩, rfl⟩

/-- A message id is received by a label exactly when the label carries the recv observation. -/
private theorem mem_recvs_iff (label : TypeLabel) (msg : MessageId) :
    msg ∈ label.recvs ↔ label.contains (.message msg .recv) := by
  cases label with
  | tock => simp [recvs, contains]
  | actions observations =>
      simp only [recvs, messageIdsWith, Finset.mem_image, Finset.mem_filter, contains]
      constructor
      · rintro ⟨observation, ⟨hMem, hDir⟩, hMsg⟩
        cases observation <;> simp_all
      · intro hMem
        exact ⟨.message msg .recv, ⟨hMem, rfl⟩, rfl⟩

/-- Synchronised message ids come from the interface. -/
private theorem synced_subset (interface : Interface) (left right : TypeLabel) :
    synced interface left right ⊆ interface := by
  intro msg hMem
  simp only [synced, Finset.mem_union, Finset.mem_inter] at hMem
  rcases hMem with ⟨hIn, _⟩ | ⟨hIn, _⟩ <;> exact hIn

/-! ## Membership in the observation set produced by `combine` -/

/-- A raw message observation survives `combine` when it is not synchronised away. -/
private theorem contains_combine_message (interface : Interface)
    (left right : Finset TypeObservation) (msg : MessageId) (dir : MessageDir) :
    (combine interface (.actions left) (.actions right)).contains (.message msg dir) ↔
      (((TypeLabel.actions left).contains (.message msg dir) ∨
          (TypeLabel.actions right).contains (.message msg dir)) ∧
        msg ∉ synced interface (.actions left) (.actions right)) := by
  simp [combine, contains, isRawSyncedMessage, Finset.mem_union, Finset.mem_filter,
    Finset.mem_image]

/-- A resolved observation is in `combine` when it is raw in a component or newly synchronised. -/
private theorem contains_combine_resolved (interface : Interface)
    (left right : Finset TypeObservation) (msg : MessageId) :
    (combine interface (.actions left) (.actions right)).contains (.resolved msg) ↔
      ((TypeLabel.actions left).contains (.resolved msg) ∨
        (TypeLabel.actions right).contains (.resolved msg) ∨
        msg ∈ synced interface (.actions left) (.actions right)) := by
  simp [combine, contains, isRawSyncedMessage, Finset.mem_union, Finset.mem_filter,
    Finset.mem_image, or_assoc]

/-- Fair observations pass through `combine` untouched. -/
private theorem contains_combine_fair (interface : Interface)
    (left right : Finset TypeObservation) (bid : BranchId) (taken : Bool) :
    (combine interface (.actions left) (.actions right)).contains (.fair bid taken) ↔
      ((TypeLabel.actions left).contains (.fair bid taken) ∨
        (TypeLabel.actions right).contains (.fair bid taken)) := by
  simp [combine, contains, isRawSyncedMessage, Finset.mem_union, Finset.mem_filter,
    Finset.mem_image]

/-- Progress observations pass through `combine` untouched. -/
private theorem contains_combine_progress (interface : Interface)
    (left right : Finset TypeObservation) (pid : ProcId) :
    (combine interface (.actions left) (.actions right)).contains (.progress pid) ↔
      ((TypeLabel.actions left).contains (.progress pid) ∨
        (TypeLabel.actions right).contains (.progress pid)) := by
  simp [combine, contains, isRawSyncedMessage, Finset.mem_union, Finset.mem_filter,
    Finset.mem_image]

/-! ## Tock propagation through `Sync` -/

/-- A clock label can only synchronise with a clock label. -/
private theorem sync_tock_left {interface : Interface} {left right : TypeLabel}
    (hSync : Sync interface left right) (hLeft : left = .tock) : right = .tock := by
  subst hLeft
  cases right with
  | tock => rfl
  | actions observations =>
      exact absurd (hSync.2.2.mp trivial) (by simp [isTock])

/-- A clock label can only synchronise with a clock label. -/
private theorem sync_tock_right {interface : Interface} {left right : TypeLabel}
    (hSync : Sync interface left right) (hRight : right = .tock) : left = .tock := by
  subst hRight
  cases left with
  | tock => rfl
  | actions observations =>
      exact absurd (hSync.2.2.mpr trivial) (by simp [isTock])

/-! ## Orientation of a synchronised message -/

/-- For a synchronised message id, one component sends it and the other receives it, and
neither component performs the other's half. -/
private theorem synced_orientation {interface : Interface} {left right : TypeLabel}
    (hSync : Sync interface left right)
    (hOwn : ∀ observation, left.contains observation → ¬ right.contains observation)
    {msg : MessageId} (hMem : msg ∈ synced interface left right) :
    (left.contains (.message msg .send) ∧ right.contains (.message msg .recv) ∧
        ¬ left.contains (.message msg .recv) ∧ ¬ right.contains (.message msg .send)) ∨
      (left.contains (.message msg .recv) ∧ right.contains (.message msg .send) ∧
        ¬ left.contains (.message msg .send) ∧ ¬ right.contains (.message msg .recv)) := by
  have hInterface : msg ∈ interface := synced_subset interface left right hMem
  have hFirst : ∀ x, x ∈ interface ∩ left.sends ↔ x ∈ interface ∩ right.recvs := by
    intro x; rw [hSync.1]
  have hSecond : ∀ x, x ∈ interface ∩ left.recvs ↔ x ∈ interface ∩ right.sends := by
    intro x; rw [hSync.2.1]
  simp only [synced, Finset.mem_union, Finset.mem_inter] at hMem
  rcases hMem with ⟨_, hLeftSend⟩ | ⟨_, hRightSend⟩
  · left
    have hL : left.contains (.message msg .send) := (mem_sends_iff _ _).mp hLeftSend
    have hR : right.contains (.message msg .recv) :=
      (mem_recvs_iff _ _).mp
        (Finset.mem_inter.mp ((hFirst msg).mp (Finset.mem_inter.mpr ⟨hInterface, hLeftSend⟩))).2
    have hNotRightSend : ¬ right.contains (.message msg .send) := hOwn _ hL
    refine ⟨hL, hR, ?_, hNotRightSend⟩
    intro hLeftRecv
    have hRightSend : msg ∈ interface ∩ right.sends :=
      (hSecond msg).mp (Finset.mem_inter.mpr ⟨hInterface, (mem_recvs_iff _ _).mpr hLeftRecv⟩)
    exact hNotRightSend ((mem_sends_iff _ _).mp (Finset.mem_inter.mp hRightSend).2)
  · right
    have hR : right.contains (.message msg .send) := (mem_sends_iff _ _).mp hRightSend
    have hL : left.contains (.message msg .recv) :=
      (mem_recvs_iff _ _).mp
        (Finset.mem_inter.mp ((hSecond msg).mpr (Finset.mem_inter.mpr ⟨hInterface, hRightSend⟩))).2
    have hNotLeftSend : ¬ left.contains (.message msg .send) := fun hc => hOwn _ hc hR
    refine ⟨hL, hR, hNotLeftSend, ?_⟩
    intro hRightRecv
    have hLeftSend : msg ∈ interface ∩ left.sends :=
      (hFirst msg).mpr (Finset.mem_inter.mpr ⟨hInterface, (mem_recvs_iff _ _).mpr hRightRecv⟩)
    exact hNotLeftSend ((mem_sends_iff _ _).mp (Finset.mem_inter.mp hLeftSend).2)

/-! ## Injectivity of `combine` -/

/-- `combine` is injective on synchronising, ownership-separated pairs of labels. -/
theorem combine_inj
    {interface : Interface} {a₁ a₂ b₁ b₂ : TypeLabel}
    (hSyncA : Sync interface a₁ a₂)
    (hSyncB : Sync interface b₁ b₂)
    (hOwnA : ∀ observation, a₁.contains observation → ¬ a₂.contains observation)
    (hOwnB : ∀ observation, b₁.contains observation → ¬ b₂.contains observation)
    (hCrossA : ∀ observation, a₁.contains observation → ¬ b₂.contains observation)
    (hCrossB : ∀ observation, b₁.contains observation → ¬ a₂.contains observation)
    (hFreshA : ∀ msg ∈ interface,
      ¬ a₁.contains (.resolved msg) ∧ ¬ a₂.contains (.resolved msg))
    (hFreshB : ∀ msg ∈ interface,
      ¬ b₁.contains (.resolved msg) ∧ ¬ b₂.contains (.resolved msg))
    (hCombine : combine interface a₁ a₂ = combine interface b₁ b₂) :
    a₁ = b₁ ∧ a₂ = b₂ := by
  cases a₁ with
  | tock =>
      have hA₂ : a₂ = .tock := sync_tock_left hSyncA rfl
      subst hA₂
      cases b₁ with
      | tock =>
          have hB₂ : b₂ = .tock := sync_tock_left hSyncB rfl
          subst hB₂
          exact ⟨rfl, rfl⟩
      | actions rightObservations =>
          cases b₂ with
          | tock =>
              exact absurd (sync_tock_right hSyncB rfl) (by simp)
          | actions moreObservations =>
              simp [combine] at hCombine
  | actions leftA =>
      cases a₂ with
      | tock => exact absurd (sync_tock_right hSyncA rfl) (by simp)
      | actions rightA =>
          cases b₁ with
          | tock =>
              have hB₂ : b₂ = .tock := sync_tock_left hSyncB rfl
              subst hB₂
              simp [combine] at hCombine
          | actions leftB =>
              cases b₂ with
              | tock => exact absurd (sync_tock_right hSyncB rfl) (by simp)
              | actions rightB =>
                  -- both sides are action labels
                  have hSyncedSubA :
                      synced interface (.actions leftA) (.actions rightA) ⊆ interface :=
                    synced_subset _ _ _
                  have hSyncedSubB :
                      synced interface (.actions leftB) (.actions rightB) ⊆ interface :=
                    synced_subset _ _ _
                  -- the synchronised ids agree
                  have hSynced :
                      synced interface (.actions leftA) (.actions rightA) =
                        synced interface (.actions leftB) (.actions rightB) := by
                    ext msg
                    constructor
                    · intro hMem
                      have hIn :=
                        (contains_combine_resolved interface leftA rightA msg).mpr
                          (Or.inr (Or.inr hMem))
                      rw [hCombine] at hIn
                      rcases (contains_combine_resolved interface leftB rightB msg).mp hIn with
                        h | h | h
                      · exact absurd h (hFreshB msg (hSyncedSubA hMem)).1
                      · exact absurd h (hFreshB msg (hSyncedSubA hMem)).2
                      · exact h
                    · intro hMem
                      have hIn :=
                        (contains_combine_resolved interface leftB rightB msg).mpr
                          (Or.inr (Or.inr hMem))
                      rw [← hCombine] at hIn
                      rcases (contains_combine_resolved interface leftA rightA msg).mp hIn with
                        h | h | h
                      · exact absurd h (hFreshA msg (hSyncedSubB hMem)).1
                      · exact absurd h (hFreshA msg (hSyncedSubB hMem)).2
                      · exact h
                  -- ownership places an observation of the union in the same component
                  have hPlace : ∀ observation : TypeObservation,
                      (((TypeLabel.actions leftA).contains observation ∨
                          (TypeLabel.actions rightA).contains observation) ↔
                        ((TypeLabel.actions leftB).contains observation ∨
                          (TypeLabel.actions rightB).contains observation)) →
                      (((TypeLabel.actions leftA).contains observation ↔
                          (TypeLabel.actions leftB).contains observation) ∧
                        ((TypeLabel.actions rightA).contains observation ↔
                          (TypeLabel.actions rightB).contains observation)) := by
                    intro observation hUnion
                    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
                    · intro hIn
                      rcases hUnion.mp (Or.inl hIn) with h | h
                      · exact h
                      · exact absurd h (hCrossA observation hIn)
                    · intro hIn
                      rcases hUnion.mpr (Or.inl hIn) with h | h
                      · exact h
                      · exact absurd h (hCrossB observation hIn)
                    · intro hIn
                      rcases hUnion.mp (Or.inr hIn) with h | h
                      · exact absurd hIn (hCrossB observation h)
                      · exact h
                    · intro hIn
                      rcases hUnion.mpr (Or.inr hIn) with h | h
                      · exact absurd hIn (hCrossA observation h)
                      · exact h
                  -- componentwise agreement, observation by observation
                  have hAgree : ∀ observation : TypeObservation,
                      ((TypeLabel.actions leftA).contains observation ↔
                          (TypeLabel.actions leftB).contains observation) ∧
                        ((TypeLabel.actions rightA).contains observation ↔
                          (TypeLabel.actions rightB).contains observation) := by
                    intro observation
                    cases observation with
                    | fair bid taken =>
                        refine hPlace _ ?_
                        rw [← contains_combine_fair interface leftA rightA,
                          ← contains_combine_fair interface leftB rightB, hCombine]
                    | progress pid =>
                        refine hPlace _ ?_
                        rw [← contains_combine_progress interface leftA rightA,
                          ← contains_combine_progress interface leftB rightB, hCombine]
                    | resolved msg =>
                        by_cases hMem : msg ∈ synced interface (.actions leftA) (.actions rightA)
                        · have hInterface : msg ∈ interface := hSyncedSubA hMem
                          exact ⟨iff_of_false (hFreshA msg hInterface).1 (hFreshB msg hInterface).1,
                            iff_of_false (hFreshA msg hInterface).2 (hFreshB msg hInterface).2⟩
                        · have hMemB : msg ∉ synced interface (.actions leftB) (.actions rightB) :=
                            hSynced ▸ hMem
                          refine hPlace _ ?_
                          have hLeft := contains_combine_resolved interface leftA rightA msg
                          have hRight := contains_combine_resolved interface leftB rightB msg
                          rw [hCombine] at hLeft
                          rw [hLeft] at hRight
                          constructor
                          · intro h
                            rcases hRight.mp (h.imp id Or.inl) with h' | h' | h'
                            · exact Or.inl h'
                            · exact Or.inr h'
                            · exact absurd h' hMemB
                          · intro h
                            rcases hRight.mpr (h.imp id Or.inl) with h' | h' | h'
                            · exact Or.inl h'
                            · exact Or.inr h'
                            · exact absurd h' hMem
                    | message msg dir =>
                        by_cases hMem : msg ∈ synced interface (.actions leftA) (.actions rightA)
                        · have hMemB : msg ∈ synced interface (.actions leftB) (.actions rightB) :=
                            hSynced ▸ hMem
                          rcases synced_orientation hSyncA hOwnA hMem with
                            ⟨hSendA, hRecvA, hNoRecvA, hNoSendA⟩ |
                            ⟨hRecvA, hSendA, hNoSendA, hNoRecvA⟩ <;>
                          rcases synced_orientation hSyncB hOwnB hMemB with
                            ⟨hSendB, hRecvB, hNoRecvB, hNoSendB⟩ |
                            ⟨hRecvB, hSendB, hNoSendB, hNoRecvB⟩
                          · cases dir with
                            | send =>
                                exact ⟨iff_of_true hSendA hSendB,
                                  iff_of_false hNoSendA hNoSendB⟩
                            | recv =>
                                exact ⟨iff_of_false hNoRecvA hNoRecvB,
                                  iff_of_true hRecvA hRecvB⟩
                          · exact absurd hSendB (hCrossA _ hSendA)
                          · exact absurd hSendA (hCrossB _ hSendB)
                          · cases dir with
                            | send =>
                                exact ⟨iff_of_false hNoSendA hNoSendB,
                                  iff_of_true hSendA hSendB⟩
                            | recv =>
                                exact ⟨iff_of_true hRecvA hRecvB,
                                  iff_of_false hNoRecvA hNoRecvB⟩
                        · have hMemB : msg ∉ synced interface (.actions leftB) (.actions rightB) :=
                            hSynced ▸ hMem
                          refine hPlace _ ?_
                          have hLeft := contains_combine_message interface leftA rightA msg dir
                          have hRight := contains_combine_message interface leftB rightB msg dir
                          rw [hCombine] at hLeft
                          rw [hLeft] at hRight
                          constructor
                          · intro h
                            exact (hRight.mp ⟨h, hMem⟩).1
                          · intro h
                            exact (hRight.mpr ⟨h, hMemB⟩).1
                  refine ⟨congrArg TypeLabel.actions ?_, congrArg TypeLabel.actions ?_⟩
                  · exact Finset.ext fun observation => (hAgree observation).1
                  · exact Finset.ext fun observation => (hAgree observation).2

/-! ## Non-vacuity and necessity of the freshness hypotheses -/

/-- A concrete exchange of the interface message `"m"`. -/
private theorem synced_example :
    synced ({"m"} : Interface)
      (.actions {TypeObservation.message "m" .send})
      (.actions {TypeObservation.message "m" .recv}) = {"m"} := by
  ext x
  simp [synced, mem_sends_iff, contains, eq_comm]

/-- The hypotheses of `combine_inj` hold of labels that really do synchronise a message. -/
theorem combine_inj_hypotheses_satisfiable :
    ∃ (interface : Interface) (a₁ a₂ b₁ b₂ : TypeLabel),
      synced interface a₁ a₂ ≠ ∅ ∧
      Sync interface a₁ a₂ ∧ Sync interface b₁ b₂ ∧
      (∀ observation, a₁.contains observation → ¬ a₂.contains observation) ∧
      (∀ observation, b₁.contains observation → ¬ b₂.contains observation) ∧
      (∀ observation, a₁.contains observation → ¬ b₂.contains observation) ∧
      (∀ observation, b₁.contains observation → ¬ a₂.contains observation) ∧
      (∀ msg ∈ interface,
        ¬ a₁.contains (.resolved msg) ∧ ¬ a₂.contains (.resolved msg)) ∧
      (∀ msg ∈ interface,
        ¬ b₁.contains (.resolved msg) ∧ ¬ b₂.contains (.resolved msg)) := by
  refine ⟨{"m"}, .actions {TypeObservation.message "m" .send},
    .actions {TypeObservation.message "m" .recv},
    .actions {TypeObservation.message "m" .send},
    .actions {TypeObservation.message "m" .recv},
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [synced_example]
    simp
  · refine ⟨?_, ?_, ?_⟩ <;> simp [sends, recvs, messageIdsWith, isTock]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [sends, recvs, messageIdsWith, isTock]
  · intro observation hIn
    simp [contains] at hIn ⊢
    simp [hIn]
  · intro observation hIn
    simp [contains] at hIn ⊢
    simp [hIn]
  · intro observation hIn
    simp [contains] at hIn ⊢
    simp [hIn]
  · intro observation hIn
    simp [contains] at hIn ⊢
    simp [hIn]
  · intro msg _
    simp [contains]
  · intro msg _
    simp [contains]

/-! ## The freshness hypotheses cannot be dropped -/

/-- Without the freshness hypotheses `combine` is not injective: a raw `resolved` observation
on one side is indistinguishable from a genuine synchronisation on the other. -/
theorem not_combine_inj_without_freshness :
    ¬ ∀ (interface : Interface) (a₁ a₂ b₁ b₂ : TypeLabel),
        Sync interface a₁ a₂ → Sync interface b₁ b₂ →
        (∀ observation, a₁.contains observation → ¬ a₂.contains observation) →
        (∀ observation, b₁.contains observation → ¬ b₂.contains observation) →
        (∀ observation, a₁.contains observation → ¬ b₂.contains observation) →
        (∀ observation, b₁.contains observation → ¬ a₂.contains observation) →
        combine interface a₁ a₂ = combine interface b₁ b₂ →
        a₁ = b₁ ∧ a₂ = b₂ := by
  intro hAll
  have hSyncedB :
      synced ({"m"} : Interface)
        (.actions {TypeObservation.resolved "m"}) (.actions ∅) = ∅ := by
    ext x
    simp [synced, mem_sends_iff, contains]
  have hCombineA :
      combine ({"m"} : Interface)
        (.actions {TypeObservation.message "m" .send})
        (.actions {TypeObservation.message "m" .recv}) =
        .actions {TypeObservation.resolved "m"} := by
    simp only [combine, synced_example]
    decide
  have hCombineB :
      combine ({"m"} : Interface)
        (.actions {TypeObservation.resolved "m"}) (.actions ∅) =
        .actions {TypeObservation.resolved "m"} := by
    simp only [combine, hSyncedB]
    decide
  have hResult :=
    hAll ({"m"} : Interface)
      (.actions {TypeObservation.message "m" .send})
      (.actions {TypeObservation.message "m" .recv})
      (.actions {TypeObservation.resolved "m"}) (.actions ∅)
      (by refine ⟨?_, ?_, ?_⟩ <;>
        simp [sends, recvs, messageIdsWith, isTock])
      (by refine ⟨?_, ?_, ?_⟩ <;>
        simp [sends, recvs, messageIdsWith, isTock])
      (by intro observation hIn; simp [contains] at hIn ⊢; simp [hIn])
      (by intro observation hIn; simp [contains])
      (by intro observation hIn; simp [contains])
      (by intro observation hIn; simp [contains] at hIn ⊢; simp [hIn])
      (hCombineA.trans hCombineB.symm)
  simp at hResult

end TypeLabel

end Pact
