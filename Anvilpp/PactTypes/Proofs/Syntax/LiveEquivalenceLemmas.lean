import Anvilpp.PactTypes.Spec.Syntax.LiveEquivalenceDefs
import Anvilpp.PactTypes.Proofs.Syntax.TypeFutureOffersFuelLemmas

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

/-- Live equivalence preserves the declarations read by offer-head gates. -/
private theorem liveEqBranches_head_gate : ∀ (bs bs' : List (BareMessage × PactType))
    (a b : PactTypeAlphabet), LiveEqBranches bs bs' →
    PactTypeAlphabet.AgreeOn a b (BranchMessageActions bs) →
    ((∀ x ∈ bs, x.1 ∈ a.actions) ↔ (∀ x ∈ bs', x.1 ∈ b.actions)) := by
  intro bs
  induction bs with
  | nil =>
      intro bs' a b h _
      cases bs' with
      | nil => simp
      | cons _ _ => simp only [LiveEqBranches] at h
  | cons head rest ihRest =>
      intro bs' a b h hAgree
      cases bs' with
      | nil => simp only [LiveEqBranches] at h
      | cons head' rest' =>
          obtain ⟨action, body⟩ := head
          obtain ⟨action', body'⟩ := head'
          simp only [LiveEqBranches] at h
          obtain ⟨rfl, -, hRest⟩ := h
          rw [BranchMessageActions] at hAgree
          have hHead : action ∈ a.actions ↔ action ∈ b.actions :=
            hAgree action (by simp)
          have hTail : PactTypeAlphabet.AgreeOn a b
              (BranchMessageActions rest) := fun act hact =>
            hAgree act (Finset.mem_union_right _ hact)
          have hRestIff := ihRest rest' a b hRest hTail
          constructor
          · intro hAll x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact hHead.mp (hAll (action, body) (by simp))
            · exact hRestIff.mp (fun y hy => hAll y (by simp [hy])) x hx'
          · intro hAll x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact hHead.mpr (hAll (action, body') (by simp))
            · exact hRestIff.mpr (fun y hy => hAll y (by simp [hy])) x hx'

/-- Completion reads only declarations of live actions. -/
theorem liveEqBody_canComplete : ∀ (fuel : Nat) (rho theta : PactType),
    LiveEqBody rho theta →
    typeCanCompleteThisCycleFuel fuel rho =
      typeCanCompleteThisCycleFuel fuel theta := by
  intro fuel
  induction fuel with
  | zero => intro rho theta _; rfl
  | succ fuel ih =>
      have branches : ∀ (bs bs' : List (BareMessage × PactType)),
          LiveEqBranches bs bs' →
          (bs.any fun branch => typeCanCompleteThisCycleFuel fuel branch.2) =
            (bs'.any fun branch =>
              typeCanCompleteThisCycleFuel fuel branch.2) := by
        intro bs
        induction bs with
        | nil =>
            intro bs' h
            cases bs' with
            | nil => rfl
            | cons _ _ => simp only [LiveEqBranches] at h
        | cons head rest ihRest =>
            intro bs' h
            cases bs' with
            | nil => simp only [LiveEqBranches] at h
            | cons head' rest' =>
                obtain ⟨action, body⟩ := head
                obtain ⟨action', body'⟩ := head'
                simp only [LiveEqBranches] at h
                obtain ⟨rfl, hBody, hRest⟩ := h
                simp only [List.any_cons, ih body body' hBody,
                  ihRest rest' hRest]
      intro rho theta hLive
      cases rho <;> cases theta <;>
        first
          | (simp only [LiveEqBody] at hLive; done)
          | skip
      case message.message =>
        simp only [LiveEqBody] at hLive
        obtain ⟨rfl, rfl, hA⟩ := hLive
        simp only [typeCanCompleteThisCycleFuel,
          hA _ (Finset.mem_singleton_self _)]
      case progress.progress => rfl
      case tock.tock => rfl
      case skip.skip => rfl
      case var.var => rfl
      case choice.choice | seq.seq =>
        simp only [LiveEqBody] at hLive
        simp only [typeCanCompleteThisCycleFuel, ih _ _ hLive.2.1, ih _ _ hLive.2.2]
      case fairChoice.fairChoice | par.par =>
        simp only [LiveEqBody] at hLive
        simp only [typeCanCompleteThisCycleFuel, ih _ _ hLive.2.2.1, ih _ _ hLive.2.2.2]
      case recur.recur =>
        simp only [LiveEqBody] at hLive
        simp only [typeCanCompleteThisCycleFuel, ih _ _ hLive.2.2]
      case xoffer.xoffer | offer.offer =>
        simp only [LiveEqBody] at hLive
        obtain ⟨hA, hElse, hBranches⟩ := hLive
        rw [MessageActions] at hA
        have hGate := liveEqBranches_head_gate _ _ _ _ hBranches
          (fun act hact => hA act (Finset.mem_union_right _ hact))
        simp only [typeCanCompleteThisCycleFuel, ih _ _ hElse,
          branches _ _ hBranches, hGate]

/-- The same-cycle menu reads an alphabet only at actions the subterm still
uses, so live equivalence preserves it at every fuel. -/
theorem liveEqBody_futureOffersFuel : ∀ (fuel : Nat) (rho theta : PactType),
    LiveEqBody rho theta →
    typeFutureOffersFuel fuel rho = typeFutureOffersFuel fuel theta := by
  intro fuel
  induction fuel with
  | zero => intro rho theta _; rfl
  | succ fuel ih =>
      have branches : ∀ (bs bs' : List (BareMessage × PactType))
          (acc acc' : Finset BareMessage), LiveEqBranches bs bs' → acc = acc' →
          bs.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2) acc =
            bs'.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2) acc' := by
        intro bs
        induction bs with
        | nil =>
            intro bs' acc acc' h hAcc
            cases bs' with
            | nil => simpa using hAcc
            | cons _ _ => simp only [LiveEqBranches] at h
        | cons head rest ihRest =>
            intro bs' acc acc' h hAcc
            cases bs' with
            | nil => simp only [LiveEqBranches] at h
            | cons head' rest' =>
                obtain ⟨action, body⟩ := head
                obtain ⟨action', body'⟩ := head'
                simp only [LiveEqBranches] at h
                obtain ⟨rfl, hBody, hRest⟩ := h
                simp only [List.foldl_cons]
                exact ihRest rest' _ _ hRest
                  (by rw [hAcc, ih body body' hBody])
      intro rho theta hLive
      cases rho <;> cases theta <;>
        first
          | (simp only [LiveEqBody] at hLive; done)
          | skip
      case message.message =>
          simp only [LiveEqBody] at hLive
          obtain ⟨rfl, rfl, hA⟩ := hLive
          simp only [typeFutureOffersFuel]
          exact if_congr (hA _ (Finset.mem_singleton_self _)) rfl rfl
      case progress.progress => rfl
      case tock.tock => rfl
      case skip.skip => rfl
      case var.var => rfl
      case choice.choice =>
          simp only [LiveEqBody] at hLive
          obtain ⟨-, hl, hr⟩ := hLive
          simp only [typeFutureOffersFuel, ih _ _ hl, ih _ _ hr]
      case fairChoice.fairChoice =>
          simp only [LiveEqBody] at hLive
          obtain ⟨-, -, hl, hr⟩ := hLive
          simp only [typeFutureOffersFuel, ih _ _ hl, ih _ _ hr]
      case seq.seq =>
          simp only [LiveEqBody] at hLive
          obtain ⟨-, hl, hr⟩ := hLive
          simp only [typeFutureOffersFuel, ih _ _ hl, ih _ _ hr,
            liveEqBody_canComplete fuel _ _ hl]
      case par.par =>
          simp only [LiveEqBody] at hLive
          obtain ⟨rfl, -, hl, hr⟩ := hLive
          simp only [typeFutureOffersFuel, ih _ _ hl, ih _ _ hr]
      case recur.recur =>
          simp only [LiveEqBody] at hLive
          obtain ⟨-, -, hb⟩ := hLive
          simp only [typeFutureOffersFuel, ih _ _ hb]
      case xoffer.xoffer | offer.offer =>
          rename_i alphabet other bs alphabet' other' bs'
          simp only [LiveEqBody] at hLive
          obtain ⟨hA, he, hbs⟩ := hLive
          rw [MessageActions] at hA
          simp only [typeFutureOffersFuel]
          rw [← branches _ _ _ _ hbs (ih _ _ he)]
          ext action
          simp only [Finset.mem_inter]
          by_cases hMenu : action ∈ bs.foldl
              (fun offers branch => offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
              (typeFutureOffersFuel fuel other)
          · have hSupport := foldl_typeMenu_subset_messageActions
              (typeFutureOffersFuel fuel) (typeFutureOffersFuel_subset_messageActions fuel)
              bs (typeFutureOffersFuel fuel other) hMenu
            have hUsed : action ∈ other.MessageActions ∪ BranchMessageActions bs :=
              Finset.union_subset_union (typeFutureOffersFuel_subset_messageActions fuel other)
                (Finset.Subset.refl _) hSupport
            exact and_congr Iff.rfl (hA action hUsed)
          · simp only [hMenu, false_and]

/-- `FutOff` agrees on live-equivalent residuals.  The two may have different
`sizeOf`, so both menus are read at one fuel large enough for either. -/
theorem liveEq_preserves_futOff {rho theta : PactType} (h : LiveEq rho theta) :
    typeFutureOffers rho = typeFutureOffers theta := by
  have hFuel : sizeOf rho + 1 ≤ max (sizeOf rho) (sizeOf theta) + 1 := by
    have := le_max_left (sizeOf rho) (sizeOf theta); omega
  have hFuel' : sizeOf theta + 1 ≤ max (sizeOf rho) (sizeOf theta) + 1 := by
    have := le_max_right (sizeOf rho) (sizeOf theta); omega
  rw [← typeFutureOffersFuel_eq_typeFutureOffers rho _ hFuel,
    ← typeFutureOffersFuel_eq_typeFutureOffers theta _ hFuel']
  exact liveEqBody_futureOffersFuel _ rho theta h.2

end PactType

end Pact
