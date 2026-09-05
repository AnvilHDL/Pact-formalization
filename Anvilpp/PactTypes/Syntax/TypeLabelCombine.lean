import Anvilpp.PactTypes.Syntax.TypeErasure

namespace Pact

namespace TypeLabel

/-! ## Membership helpers for `sends`, `recvs` and `synced` -/

/-- A message id is sent by a label exactly when the label carries the send observation. -/
theorem mem_sends_iff (label : TypeLabel) (msg : MessageId) :
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

/-! ## Membership in the observation set produced by `combine` -/

/-! ## Tock propagation through `Sync` -/

/-! ## Orientation of a synchronised message -/

/-! ## Injectivity of `combine` -/

/-! ## Non-vacuity and necessity of the freshness hypotheses -/

/-! ## The freshness hypotheses cannot be dropped -/

end TypeLabel

end Pact
