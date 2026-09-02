import Anvilpp.PactTypes.Syntax.LiveEquivalenceDefs

/-!
Live equivalence is an equivalence relation, and it does not change which
residuals have completed.
-/

namespace Pact

namespace PactType

mutual

theorem liveEqBody_refl : ∀ rho : PactType, LiveEqBody rho rho
  | .message a m d => by
      rw [LiveEqBody]; exact ⟨rfl, rfl, PactTypeAlphabet.AgreeOn.refl _ _⟩
  | .progress _ _ => by rw [LiveEqBody]
  | .tock _ => by rw [LiveEqBody]; trivial
  | .skip _ => by rw [LiveEqBody]; trivial
  | .var _ _ => by rw [LiveEqBody]
  | .choice a l r => by
      rw [LiveEqBody]
      exact ⟨PactTypeAlphabet.AgreeOn.refl _ _, liveEqBody_refl l,
        liveEqBody_refl r⟩
  | .seq a l r => by
      rw [LiveEqBody]
      exact ⟨PactTypeAlphabet.AgreeOn.refl _ _, liveEqBody_refl l,
        liveEqBody_refl r⟩
  | .fairChoice a bid l r => by
      rw [LiveEqBody]
      exact ⟨rfl, PactTypeAlphabet.AgreeOn.refl _ _, liveEqBody_refl l,
        liveEqBody_refl r⟩
  | .par a l r i => by
      rw [LiveEqBody]
      exact ⟨rfl, PactTypeAlphabet.AgreeOn.refl _ _, liveEqBody_refl l,
        liveEqBody_refl r⟩
  | .recur a n body => by
      rw [LiveEqBody]
      exact ⟨rfl, PactTypeAlphabet.AgreeOn.refl _ _, liveEqBody_refl body⟩
  | .xoffer a e bs => by
      rw [LiveEqBody]
      exact ⟨PactTypeAlphabet.AgreeOn.refl _ _, liveEqBody_refl e,
        liveEqBranches_refl bs⟩
  | .offer a e bs => by
      rw [LiveEqBody]
      exact ⟨PactTypeAlphabet.AgreeOn.refl _ _, liveEqBody_refl e,
        liveEqBranches_refl bs⟩
  termination_by rho => sizeOf rho

theorem liveEqBranches_refl :
    ∀ branches : List (BareMessage × PactType), LiveEqBranches branches branches
  | [] => by rw [LiveEqBranches]; trivial
  | (action, body) :: rest => by
      rw [LiveEqBranches]
      exact ⟨rfl, liveEqBody_refl body, liveEqBranches_refl rest⟩
  termination_by branches => sizeOf branches

end

theorem liveEq_refl (rho : PactType) : LiveEq rho rho :=
  ⟨rfl, liveEqBody_refl rho⟩

/-- Live-equivalent residuals use the same message actions: the relation forces
the same control skeleton, and `MessageActions` reads only that. -/
theorem liveEqBody_messageActions : ∀ (n : Nat) (rho theta : PactType),
    sizeOf rho ≤ n → LiveEqBody rho theta →
    MessageActions rho = MessageActions theta := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have branches : ∀ (bs bs' : List (BareMessage × PactType)),
        sizeOf bs < n → LiveEqBranches bs bs' →
        BranchMessageActions bs = BranchMessageActions bs' := by
      intro bs
      induction bs with
      | nil =>
          intro bs' _ h
          cases bs' with
          | nil => simp [BranchMessageActions]
          | cons _ _ => simp only [LiveEqBranches] at h
      | cons head rest ihRest =>
          intro bs' hSize h
          cases bs' with
          | nil => simp only [LiveEqBranches] at h
          | cons head' rest' =>
              obtain ⟨action, body⟩ := head
              obtain ⟨action', body'⟩ := head'
              simp only [LiveEqBranches] at h
              obtain ⟨rfl, hBody, hRest⟩ := h
              have hBodySize : sizeOf body < n := by
                simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
                omega
              have hRestSize : sizeOf rest < n := by
                simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
                omega
              rw [BranchMessageActions, BranchMessageActions,
                ih (sizeOf body) hBodySize body body' le_rfl hBody,
                ihRest rest' hRestSize hRest]
    intro rho theta hSize hLive
    cases rho <;> cases theta <;>
      first
        | (simp only [LiveEqBody] at hLive; done)
        | (simp only [LiveEqBody] at hLive
           obtain ⟨rfl, rfl, -⟩ := hLive
           simp [MessageActions]
           done)
        | (simp only [LiveEqBody] at hLive
           simp only [MessageActions]
           try obtain ⟨rfl, rfl, -⟩ := hLive
           try rfl
           done)
        | (simp only [LiveEqBody] at hLive
           simp only [MessageActions]
           first
             | (rw [ih _ (by simp only [PactType.choice.sizeOf_spec, PactType.seq.sizeOf_spec, PactType.par.sizeOf_spec, PactType.fairChoice.sizeOf_spec, PactType.recur.sizeOf_spec, PactType.xoffer.sizeOf_spec, PactType.offer.sizeOf_spec] at hSize <;> omega) _ _ le_rfl hLive.2.1,
                  ih _ (by simp only [PactType.choice.sizeOf_spec, PactType.seq.sizeOf_spec, PactType.par.sizeOf_spec, PactType.fairChoice.sizeOf_spec, PactType.recur.sizeOf_spec, PactType.xoffer.sizeOf_spec, PactType.offer.sizeOf_spec] at hSize <;> omega) _ _ le_rfl hLive.2.2]; done)
             | (rw [ih _ (by simp only [PactType.choice.sizeOf_spec, PactType.seq.sizeOf_spec, PactType.par.sizeOf_spec, PactType.fairChoice.sizeOf_spec, PactType.recur.sizeOf_spec, PactType.xoffer.sizeOf_spec, PactType.offer.sizeOf_spec] at hSize <;> omega) _ _ le_rfl hLive.2.2.1,
                  ih _ (by simp only [PactType.choice.sizeOf_spec, PactType.seq.sizeOf_spec, PactType.par.sizeOf_spec, PactType.fairChoice.sizeOf_spec, PactType.recur.sizeOf_spec, PactType.xoffer.sizeOf_spec, PactType.offer.sizeOf_spec] at hSize <;> omega) _ _ le_rfl hLive.2.2.2]; done)
             | (rw [ih _ (by simp only [PactType.choice.sizeOf_spec, PactType.seq.sizeOf_spec, PactType.par.sizeOf_spec, PactType.fairChoice.sizeOf_spec, PactType.recur.sizeOf_spec, PactType.xoffer.sizeOf_spec, PactType.offer.sizeOf_spec] at hSize <;> omega) _ _ le_rfl hLive.2.2]; done)
             | (rw [ih _ (by simp only [PactType.choice.sizeOf_spec, PactType.seq.sizeOf_spec, PactType.par.sizeOf_spec, PactType.fairChoice.sizeOf_spec, PactType.recur.sizeOf_spec, PactType.xoffer.sizeOf_spec, PactType.offer.sizeOf_spec] at hSize <;> omega) _ _ le_rfl hLive.2.1,
                  branches _ _ (by simp only [PactType.choice.sizeOf_spec, PactType.seq.sizeOf_spec, PactType.par.sizeOf_spec, PactType.fairChoice.sizeOf_spec, PactType.recur.sizeOf_spec, PactType.xoffer.sizeOf_spec, PactType.offer.sizeOf_spec] at hSize <;> omega) hLive.2.2]; done))

end PactType

end Pact
