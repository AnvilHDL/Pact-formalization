import Anvilpp.ProofHelpers.Inference.RepresentedResiduals

/-!
# Prerequisites for decorated-step lifting

Expression progress, the shape of a process whose abstraction is a given type
constructor, non-clock steps, and the label agreement the lifting maintains:
after erasure a lifted label differs from the recorded one at most in
fair-choice outcomes, so it agrees on message observations and on the clock.
-/

namespace Pact

noncomputable section

open Classical

/-! ## Expression progress -/

theorem exprEval_of_closed :
    ∀ expr : Expr, Expr.AllVariablesBound [] expr → ∃ value, Semantics.ExprEval expr value := by
  intro expr
  induction expr with
  | var name => intro hBound; exact absurd hBound (by simp [Expr.AllVariablesBound])
  | val value => intro _; exact ⟨value, Semantics.ExprEval.literal value⟩
  | bin left bop right ihLeft ihRight =>
      intro hBound
      obtain ⟨leftValue, hLeft⟩ := ihLeft hBound.1
      obtain ⟨rightValue, hRight⟩ := ihRight hBound.2
      exact ⟨valEval leftValue rightValue bop,
        Semantics.ExprEval.bin _ _ _ _ _ hLeft hRight⟩

/-! ## Shapes -/

theorem inferProcess_eq_seq {process : Proc} {alphabet : PactTypeAlphabet}
    {left right : PactType} (h : inferProcess process = .seq alphabet left right) :
    (∃ msg expr p, process = Proc.send alphabet msg expr p ∧
        left = .message alphabet msg MessageDir.send ∧ right = inferProcess p) ∨
    (∃ msg varName p, process = Proc.recv alphabet msg varName p ∧
        left = .message alphabet msg MessageDir.recv ∧ right = inferProcess p) ∨
    (∃ varName expr p, process = Proc.letp alphabet varName expr p ∧
        left = .skip alphabet ∧ right = inferProcess p) ∨
    (∃ l r, process = Proc.seq alphabet l r ∧
        left = inferProcess l ∧ right = inferProcess r) := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_choice {process : Proc} {alphabet : PactTypeAlphabet}
    {left right : PactType}
    (h : inferProcess process = .choice alphabet left right) :
    ∃ expr l r, process = Proc.ifunfair alphabet expr l r ∧
      left = inferProcess l ∧ right = inferProcess r := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_fairChoice {process : Proc} {alphabet : PactTypeAlphabet}
    {bid : BranchId} {left right : PactType}
    (h : inferProcess process = .fairChoice alphabet bid left right) :
    ∃ expr l r, process = Proc.iffair alphabet bid expr l r ∧
      left = inferProcess l ∧ right = inferProcess r := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_par {process : Proc} {alphabet : PactTypeAlphabet}
    {left right : PactType} {interface : Interface}
    (h : inferProcess process = .par alphabet left right interface) :
    ∃ l r, process = Proc.par alphabet l r interface ∧
      left = inferProcess l ∧ right = inferProcess r := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_recur {process : Proc} {alphabet : PactTypeAlphabet}
    {name : String} {body : PactType}
    (h : inferProcess process = .recur alphabet name body) :
    ∃ b, process = Proc.recur alphabet name b ∧ body = inferProcess b := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_xoffer {process : Proc} {alphabet : PactTypeAlphabet}
    {elseType : PactType} {branches : List (BareMessage × PactType)}
    (h : inferProcess process = .xoffer alphabet elseType branches) :
    ∃ elseProcess processBranches,
      process = Proc.xoffer alphabet elseProcess processBranches ∧
        elseType = inferProcess elseProcess ∧
        branches = inferBranches processBranches := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_offer {process : Proc} {alphabet : PactTypeAlphabet}
    {elseType : PactType} {branches : List (BareMessage × PactType)}
    (h : inferProcess process = .offer alphabet elseType branches) :
    ∃ elseProcess processBranches,
      process = Proc.offer alphabet elseProcess processBranches ∧
        elseType = inferProcess elseProcess ∧
        branches = inferBranches processBranches := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_tock {process : Proc} {alphabet : PactTypeAlphabet}
    (h : inferProcess process = .tock alphabet) :
    process = Proc.cycle alphabet := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_progress {process : Proc} {alphabet : PactTypeAlphabet}
    {pid : ProcId} (h : inferProcess process = .progress alphabet pid) :
    process = Proc.endp alphabet pid := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_message {process : Proc} {alphabet : PactTypeAlphabet}
    {msg : MessageId} {dir : MessageDir}
    (h : inferProcess process = .message alphabet msg dir) : False := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

theorem inferProcess_eq_var {process : Proc} {alphabet : PactTypeAlphabet}
    {name : String} (h : inferProcess process = .var alphabet name) :
    process = Proc.var alphabet name := by
  cases process <;> rw [inferProcess] at h <;> simp_all <;>
    (try (obtain ⟨rfl, hLeft, hRight⟩ := h; exact hLeft.symm)) <;>
    (try (obtain ⟨rfl, hLeft⟩ := h; exact hLeft.symm)) <;>
    (try exact h.symm) <;> (try tauto)

/-- A branch of `abs_B(B)` comes from a branch of `B`. -/
theorem exists_branch_of_mem_inferBranches :
    ∀ {branches : List ChoiceBranch} {entry : BareMessage × PactType},
      entry ∈ inferBranches branches →
        ∃ branch ∈ branches, inferBranch branch = entry := by
  intro branches
  induction branches with
  | nil => intro entry hMem; rw [inferBranches] at hMem; exact absurd hMem (by simp)
  | cons head rest ih =>
      intro entry hMem
      rw [inferBranches_cons] at hMem
      rcases List.mem_cons.1 hMem with rfl | hTail
      · exact ⟨head, List.mem_cons_self, rfl⟩
      · obtain ⟨branch, hBranch, hEq⟩ := ih hTail
        exact ⟨branch, List.mem_cons_of_mem _ hBranch, hEq⟩

/-! ## Clock status -/

theorem Label.combine_eq_tock_iff (interface : Interface) (left right : Label) :
    Label.combine interface left right = Label.tock ↔
      left = Label.tock ∧ right = Label.tock := by
  cases left <;> cases right <;>
    simp [Label.combine, Label.silent]

theorem LocalOfferEnvironment.clock_false {outer siblingEnv localEnv : Environment}
    {interface : Interface} {localProc : Proc} {current : Finset Offer}
    {future : Finset BareMessage}
    (hLocal : LocalOfferEnvironment outer interface localProc siblingEnv current
      future localEnv) (hOuter : outer.clock = false) : localEnv.clock = false := by
  cases hLocal with
  | clock _ _ _ _ hClockOuter => exact absurd hClockOuter (by rw [hOuter]; simp)
  | ordinary _ _ _ _ _ _ _ _ hLocalClock _ _ => exact hLocalClock

/-- Under a non-clock environment no process step observes the clock. -/
theorem Offers.label_ne_tock {env : Environment} {source target : Proc}
    {label : Label} {current : Finset Offer} {future : Finset BareMessage}
    (hOffers : Offers env source label target current future)
    (hClock : env.clock = false) : label ≠ Label.tock := by
  induction hOffers with
  | send _ _ _ _ _ _ _ _ => simp [Label.message]
  | send_wait _ _ _ _ _ _ _ _ => simp [Label.silent]
  | recv _ _ _ _ _ _ _ _ => simp [Label.message]
  | recv_wait _ _ _ _ _ _ _ => simp [Label.silent]
  | cycle env _ hPrem => exact absurd hPrem.2 (by rw [hClock]; simp)
  | cycle_wait _ _ _ => simp [Label.silent]
  | skip _ _ _ => simp [Label.silent]
  | progress _ _ _ _ => simp [Label.progress]
  | letp _ _ _ _ _ _ _ => simp [Label.silent]
  | if_true _ _ _ _ _ _ => simp [Label.silent]
  | if_false _ _ _ _ _ _ => simp [Label.silent]
  | fair_true _ _ _ _ _ _ _ => simp [Label.fair]
  | fair_false _ _ _ _ _ _ _ => simp [Label.fair]
  | recur _ _ _ _ _ => simp [Label.silent]
  | seq _ _ _ _ _ _ _ _ _ _ hTock _ => exact hTock
  | seq_tock _ _ _ _ _ _ _ hOffers _ ih => exact absurd rfl (ih hClock)
  | seq_fuse _ _ _ _ _ _ _ _ _ hTock _ => exact hTock
  | seq_fuse_tock _ _ _ _ _ _ _ hOffers ih => exact absurd rfl (ih hClock)
  | xoffer_send _ _ _ _ _ _ _ _ _ _ => simp [Label.message]
  | xoffer_recv _ _ _ _ _ _ _ _ _ _ => simp [Label.message]
  | xoffer_else _ _ _ _ _ _ => simp [Label.silent]
  | xoffer_wait _ _ _ _ _ _ => simp [Label.silent]
  | offer_some _ _ _ _ _ _ _ => simp [Label.silent]
  | offer_else _ _ _ _ _ _ => simp [Label.silent]
  | offer_wait _ _ _ _ _ _ => simp [Label.silent]
  | par outer _ _ interface _ _ _ _ _ leftLabel rightLabel _ _ _ _ _ _ _ _ _
      hLocalLeft _ _ ihLeft _ =>
      intro hAbsurd
      exact ihLeft (hLocalLeft.clock_false hClock)
        (((Label.combine_eq_tock_iff interface leftLabel rightLabel).1 hAbsurd).1)
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ _ => exact hNotTock
  | par_fuse_tock outer _ _ interface _ _ _ leftLabel rightLabel _ _ _ _ _ _
      hLocalLeft _ _ hTock ihLeft _ =>
      exact absurd (((Label.combine_eq_tock_iff interface leftLabel rightLabel).1
        hTock).1) (ihLeft (hLocalLeft.clock_false hClock))
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocalLeft hLocalRight _ _
      _ ihRight => exact ihRight (hLocalRight.clock_false hClock)
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLocalLeft hLocalRight _ _
      _ ihLeft => exact ihLeft (hLocalLeft.clock_false hClock)

/-- The only step of `skip` is its silent stutter, with the empty pair. -/
theorem Offers.skip_inversion {env : Environment} {alphabet : PactTypeAlphabet}
    {label : Label} {target : Proc} {current : Finset Offer}
    {future : Finset BareMessage}
    (hOffers : Offers env (Proc.skip alphabet) label target current future) :
    label = Label.silent ∧ target = Proc.skip alphabet ∧ current = ∅ ∧
      future = ∅ ∧ env.clock = false := by
  cases hOffers with
  | skip _ _ hPrem =>
      refine ⟨rfl, rfl, rfl, ?_, hPrem.2⟩
      rw [procFutureOffers_inferProcess, inferProcess_skip, typeFutureOffers_skip]

/-! ## Label agreement -/

theorem Label.mem_sends_actions (msg : MessageId) (observations : Finset Observation) :
    msg ∈ (Label.actions observations).sends ↔
      ∃ value, Observation.message msg MessageDir.send value ∈ observations := by
  simp only [Label.sends, Label.messageIdsWith, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨observation, ⟨hMem, hDir⟩, hMsg⟩
    cases observation with
    | message m dir value =>
        refine ⟨value, ?_⟩
        rw [← hMsg, ← hDir]
        exact hMem
    | resolved _ => exact hDir.elim
    | fair _ _ => exact hDir.elim
    | progress _ => exact hDir.elim
  · rintro ⟨value, hMem⟩
    exact ⟨Observation.message msg MessageDir.send value, ⟨hMem, rfl⟩, rfl⟩

theorem Label.mem_recvs_actions (msg : MessageId) (observations : Finset Observation) :
    msg ∈ (Label.actions observations).recvs ↔
      ∃ value, Observation.message msg MessageDir.recv value ∈ observations := by
  simp only [Label.recvs, Label.messageIdsWith, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨observation, ⟨hMem, hDir⟩, hMsg⟩
    cases observation with
    | message m dir value =>
        refine ⟨value, ?_⟩
        rw [← hMsg, ← hDir]
        exact hMem
    | resolved _ => exact hDir.elim
    | fair _ _ => exact hDir.elim
    | progress _ => exact hDir.elim
  · rintro ⟨value, hMem⟩
    exact ⟨Observation.message msg MessageDir.recv value, ⟨hMem, rfl⟩, rfl⟩

theorem TypeLabel.mem_sends_actions (msg : MessageId)
    (observations : Finset TypeObservation) :
    msg ∈ (TypeLabel.actions observations).sends ↔
      TypeObservation.message msg MessageDir.send ∈ observations := by
  simp only [TypeLabel.sends, TypeLabel.messageIdsWith, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨observation, ⟨hMem, hDir⟩, hMsg⟩
    cases observation <;> simp_all
  · intro hMem
    exact ⟨TypeObservation.message msg MessageDir.send, ⟨hMem, rfl⟩, rfl⟩

theorem TypeLabel.mem_recvs_actions (msg : MessageId)
    (observations : Finset TypeObservation) :
    msg ∈ (TypeLabel.actions observations).recvs ↔
      TypeObservation.message msg MessageDir.recv ∈ observations := by
  simp only [TypeLabel.recvs, TypeLabel.messageIdsWith, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨observation, ⟨hMem, hDir⟩, hMsg⟩
    cases observation <;> simp_all
  · intro hMem
    exact ⟨TypeObservation.message msg MessageDir.recv, ⟨hMem, rfl⟩, rfl⟩

theorem Label.mem_sends_combine (interface : Interface)
    (left right : Finset Observation) (msg : MessageId) :
    msg ∈ (Label.combine interface (.actions left) (.actions right)).sends ↔
      (msg ∈ (Label.actions left).sends ∨ msg ∈ (Label.actions right).sends) ∧
        msg ∉ Label.synced interface (.actions left) (.actions right) := by
  rw [Label.combine, Label.mem_sends_actions]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image,
    Label.mem_sends_actions, Label.isRawSyncedMessage, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨value, hMem | ⟨action, hAction, hEq⟩⟩
    · exact ⟨hMem.1.imp (fun h => ⟨value, h⟩) (fun h => ⟨value, h⟩), hMem.2⟩
    · exact absurd hEq (by simp)
  · rintro ⟨hMem, hNotSynced⟩
    rcases hMem with ⟨value, hValue⟩ | ⟨value, hValue⟩
    · exact ⟨value, Or.inl ⟨Or.inl hValue, hNotSynced⟩⟩
    · exact ⟨value, Or.inl ⟨Or.inr hValue, hNotSynced⟩⟩

theorem Label.mem_recvs_combine (interface : Interface)
    (left right : Finset Observation) (msg : MessageId) :
    msg ∈ (Label.combine interface (.actions left) (.actions right)).recvs ↔
      (msg ∈ (Label.actions left).recvs ∨ msg ∈ (Label.actions right).recvs) ∧
        msg ∉ Label.synced interface (.actions left) (.actions right) := by
  rw [Label.combine, Label.mem_recvs_actions]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image,
    Label.mem_recvs_actions, Label.isRawSyncedMessage, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨value, hMem | ⟨action, hAction, hEq⟩⟩
    · exact ⟨hMem.1.imp (fun h => ⟨value, h⟩) (fun h => ⟨value, h⟩), hMem.2⟩
    · exact absurd hEq (by simp)
  · rintro ⟨hMem, hNotSynced⟩
    rcases hMem with ⟨value, hValue⟩ | ⟨value, hValue⟩
    · exact ⟨value, Or.inl ⟨Or.inl hValue, hNotSynced⟩⟩
    · exact ⟨value, Or.inl ⟨Or.inr hValue, hNotSynced⟩⟩

theorem TypeLabel.mem_sends_combine (interface : Interface)
    (left right : Finset TypeObservation) (msg : MessageId) :
    msg ∈ (TypeLabel.combine interface (.actions left) (.actions right)).sends ↔
      (msg ∈ (TypeLabel.actions left).sends ∨ msg ∈ (TypeLabel.actions right).sends) ∧
        msg ∉ TypeLabel.synced interface (.actions left) (.actions right) := by
  rw [TypeLabel.combine, TypeLabel.mem_sends_actions]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image,
    TypeLabel.mem_sends_actions, TypeLabel.isRawSyncedMessage, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro (hMem | ⟨action, hAction, hEq⟩)
    · exact ⟨hMem.1, hMem.2⟩
    · exact absurd hEq (by simp)
  · rintro ⟨hMem, hNotSynced⟩
    exact Or.inl ⟨hMem, hNotSynced⟩

theorem TypeLabel.mem_recvs_combine (interface : Interface)
    (left right : Finset TypeObservation) (msg : MessageId) :
    msg ∈ (TypeLabel.combine interface (.actions left) (.actions right)).recvs ↔
      (msg ∈ (TypeLabel.actions left).recvs ∨ msg ∈ (TypeLabel.actions right).recvs) ∧
        msg ∉ TypeLabel.synced interface (.actions left) (.actions right) := by
  rw [TypeLabel.combine, TypeLabel.mem_recvs_actions]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image,
    TypeLabel.mem_recvs_actions, TypeLabel.isRawSyncedMessage, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro (hMem | ⟨action, hAction, hEq⟩)
    · exact ⟨hMem.1, hMem.2⟩
    · exact absurd hEq (by simp)
  · rintro ⟨hMem, hNotSynced⟩
    exact Or.inl ⟨hMem, hNotSynced⟩

/-- After erasure the lifted label agrees with the recorded one on message
observations and on the clock; they may differ in fair-choice outcomes. -/
def LabelAgree (typeLabel : TypeLabel) (label : Label) : Prop :=
  typeLabel.sends = label.sends ∧ typeLabel.recvs = label.recvs ∧
    (typeLabel.isTock ↔ label.isTock)

theorem labelAgree_eraseLabel (label : Label) : LabelAgree (eraseLabel label) label :=
  ⟨sends_eraseLabel label, recvs_eraseLabel label, isTock_eraseLabel label⟩

theorem LabelAgree.sync {interface : Interface} {typeLeft typeRight : TypeLabel}
    {left right : Label} (hLeft : LabelAgree typeLeft left)
    (hRight : LabelAgree typeRight right)
    (hSync : TypeLabel.Sync interface typeLeft typeRight) :
    Label.Sync interface left right := by
  obtain ⟨hLeftSends, hLeftRecvs, hLeftTock⟩ := hLeft
  obtain ⟨hRightSends, hRightRecvs, hRightTock⟩ := hRight
  obtain ⟨hSends, hRecvs, hTock⟩ := hSync
  exact ⟨by rw [← hLeftSends, ← hRightRecvs]; exact hSends,
    by rw [← hLeftRecvs, ← hRightSends]; exact hRecvs,
    by rw [← hLeftTock, ← hRightTock]; exact hTock⟩

theorem LabelAgree.synced_eq {interface : Interface}
    {typeLeft typeRight : TypeLabel} {left right : Label}
    (hLeft : LabelAgree typeLeft left) (hRight : LabelAgree typeRight right) :
    TypeLabel.synced interface typeLeft typeRight =
      Label.synced interface left right := by
  unfold TypeLabel.synced Label.synced
  rw [hLeft.1, hRight.1]

theorem LabelAgree.combine {interface : Interface} {typeLeft typeRight : TypeLabel}
    {left right : Label} (hLeft : LabelAgree typeLeft left)
    (hRight : LabelAgree typeRight right) :
    LabelAgree (TypeLabel.combine interface typeLeft typeRight)
      (Label.combine interface left right) := by
  have hSynced := LabelAgree.synced_eq (interface := interface) hLeft hRight
  have hSilent : LabelAgree TypeLabel.silent Label.silent := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [TypeLabel.silent, Label.silent, TypeLabel.sends, Label.sends,
        TypeLabel.recvs, Label.recvs, TypeLabel.messageIdsWith,
        Label.messageIdsWith, TypeLabel.isTock, Label.isTock]
  cases typeLeft with
  | tock =>
      cases left with
      | actions L =>
          exact absurd hLeft.2.2 (by simp [TypeLabel.isTock, Label.isTock])
      | tock =>
          cases typeRight with
          | tock =>
              cases right with
              | actions R =>
                  exact absurd hRight.2.2 (by simp [TypeLabel.isTock, Label.isTock])
              | tock => exact ⟨rfl, rfl, Iff.rfl⟩
          | actions TR =>
              cases right with
              | tock =>
                  exact absurd hRight.2.2 (by simp [TypeLabel.isTock, Label.isTock])
              | actions R =>
                  rw [TypeLabel.combine, Label.combine]
                  exact hSilent
                  all_goals simp
  | actions TL =>
      cases left with
      | tock =>
          exact absurd hLeft.2.2 (by simp [TypeLabel.isTock, Label.isTock])
      | actions L =>
          cases typeRight with
          | tock =>
              cases right with
              | actions R =>
                  exact absurd hRight.2.2 (by simp [TypeLabel.isTock, Label.isTock])
              | tock =>
                  rw [TypeLabel.combine, Label.combine]
                  exact hSilent
                  all_goals simp
          | actions TR =>
              cases right with
              | tock =>
                  exact absurd hRight.2.2 (by simp [TypeLabel.isTock, Label.isTock])
              | actions R =>
                  refine ⟨?_, ?_, ?_⟩
                  · ext msg
                    rw [TypeLabel.mem_sends_combine, Label.mem_sends_combine,
                      hLeft.1, hRight.1, hSynced]
                  · ext msg
                    rw [TypeLabel.mem_recvs_combine, Label.mem_recvs_combine,
                      hLeft.2.1, hRight.2.1, hSynced]
                  · simp [TypeLabel.combine, Label.combine, TypeLabel.isTock,
                      Label.isTock]

end

end Pact
