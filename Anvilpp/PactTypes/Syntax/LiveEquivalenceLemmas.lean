import Anvilpp.PactTypes.Syntax.LiveEquivalenceDefs
import Anvilpp.PactTypes.Syntax.TypeFutureOffersFuelLemmas

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

/-- Live equivalence does not change whether a residual has completed. -/
theorem liveEqBody_skip_iff {rho theta : PactType} (h : LiveEqBody rho theta) :
    (∃ a, rho = .skip a) ↔ ∃ b, theta = .skip b := by
  cases rho <;> cases theta <;>
    first
      | (simp only [LiveEqBody] at h; done)
      | (constructor <;> (intro _; exact ⟨_, rfl⟩))
      | (constructor <;> (rintro ⟨a, hEq⟩; simp at hEq))

theorem liveEq_skip_iff {rho theta : PactType} (h : LiveEq rho theta) :
    (∃ a, rho = .skip a) ↔ ∃ b, theta = .skip b :=
  liveEqBody_skip_iff h.2

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

/-- Fuel-free form of `liveEqBody_messageActions`. -/
theorem liveEqBody_messageActions' {rho theta : PactType}
    (h : LiveEqBody rho theta) : MessageActions rho = MessageActions theta :=
  liveEqBody_messageActions (sizeOf rho) rho theta le_rfl h

theorem liveEqBranches_messageActions' :
    ∀ {bs bs' : List (BareMessage × PactType)}, LiveEqBranches bs bs' →
      BranchMessageActions bs = BranchMessageActions bs'
  | [], [], _ => by simp [BranchMessageActions]
  | (action, body) :: rest, (action', body') :: rest', h => by
      simp only [LiveEqBranches] at h
      obtain ⟨rfl, hBody, hRest⟩ := h
      rw [BranchMessageActions, BranchMessageActions,
        liveEqBody_messageActions' hBody,
        liveEqBranches_messageActions' hRest]
  | [], _ :: _, h => by simp only [LiveEqBranches] at h
  | _ :: _, [], h => by simp only [LiveEqBranches] at h
  termination_by bs => sizeOf bs

theorem liveEqBody_symm_fuel : ∀ (n : Nat) (rho theta : PactType),
    sizeOf rho ≤ n → LiveEqBody rho theta → LiveEqBody theta rho := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro rho theta hSize hLive
    have hMA := liveEqBody_messageActions' hLive
    have step : ∀ (x y : PactType), sizeOf x < sizeOf rho → LiveEqBody x y →
        LiveEqBody y x := fun x y hx hxy =>
      ih (sizeOf x) (lt_of_lt_of_le hx hSize) x y le_rfl hxy
    have stepBranches : ∀ (bs bs' : List (BareMessage × PactType)),
        sizeOf bs < sizeOf rho → LiveEqBranches bs bs' →
        LiveEqBranches bs' bs := by
      intro bs
      induction bs with
      | nil =>
          intro bs' _ h
          cases bs' with
          | nil => simp only [LiveEqBranches]
          | cons _ _ => simp only [LiveEqBranches] at h
      | cons head rest ihRest =>
          intro bs' hbs h
          cases bs' with
          | nil => simp only [LiveEqBranches] at h
          | cons head' rest' =>
              obtain ⟨action, body⟩ := head
              obtain ⟨action', body'⟩ := head'
              simp only [LiveEqBranches] at h ⊢
              obtain ⟨rfl, hBody, hRest⟩ := h
              simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hbs
              exact ⟨rfl, step body body' (by omega) hBody,
                ihRest rest' (by omega) hRest⟩
    cases rho <;> cases theta <;>
      first
        | (simp only [LiveEqBody] at hLive; done)
        | (simp only [LiveEqBody] at hLive ⊢
           obtain ⟨rfl, rfl, hA⟩ := hLive
           exact ⟨rfl, rfl, hA.symm⟩)
        | (simp only [LiveEqBody] at hLive ⊢; exact hLive.symm)
        | (simp only [LiveEqBody]; done)
        | (simp only [LiveEqBody] at hLive ⊢
           refine ⟨hMA ▸ hLive.1.symm,
             step _ _ (by simp only [PactType.choice.sizeOf_spec,
               PactType.seq.sizeOf_spec]; omega) hLive.2.1,
             step _ _ (by simp only [PactType.choice.sizeOf_spec,
               PactType.seq.sizeOf_spec]; omega) hLive.2.2⟩)
        | (simp only [LiveEqBody] at hLive ⊢
           refine ⟨hLive.1.symm, hMA ▸ hLive.2.1.symm,
             step _ _ (by simp only [PactType.fairChoice.sizeOf_spec,
               PactType.par.sizeOf_spec]; omega) hLive.2.2.1,
             step _ _ (by simp only [PactType.fairChoice.sizeOf_spec,
               PactType.par.sizeOf_spec]; omega) hLive.2.2.2⟩)
        | (simp only [LiveEqBody] at hLive ⊢
           refine ⟨hLive.1.symm,
             (liveEqBody_messageActions' hLive.2.2) ▸ hLive.2.1.symm,
             step _ _ (by simp only [PactType.recur.sizeOf_spec]; omega)
               hLive.2.2⟩)
        | (simp only [LiveEqBody] at hLive ⊢
           refine ⟨hMA ▸ hLive.1.symm,
             step _ _ (by simp only [PactType.xoffer.sizeOf_spec,
               PactType.offer.sizeOf_spec]; omega) hLive.2.1,
             stepBranches _ _ (by simp only [PactType.xoffer.sizeOf_spec,
               PactType.offer.sizeOf_spec]; omega) hLive.2.2⟩)

theorem liveEqBody_symm {rho theta : PactType} (h : LiveEqBody rho theta) :
    LiveEqBody theta rho :=
  liveEqBody_symm_fuel (sizeOf rho) rho theta le_rfl h

/-- Live equivalence is symmetric.  The per-node agreement set is indexed on the
left residual's own actions, so flipping the pair needs `messageActions'`. -/
theorem liveEqBranches_symm :
    ∀ {bs bs' : List (BareMessage × PactType)}, LiveEqBranches bs bs' →
      LiveEqBranches bs' bs
  | [], [], _ => by simp only [LiveEqBranches]
  | (action, body) :: rest, (action', body') :: rest', h => by
      simp only [LiveEqBranches] at h ⊢
      obtain ⟨rfl, hBody, hRest⟩ := h
      exact ⟨rfl, liveEqBody_symm hBody, liveEqBranches_symm hRest⟩
  | [], _ :: _, h => by simp only [LiveEqBranches] at h
  | _ :: _, [], h => by simp only [LiveEqBranches] at h
  termination_by bs => sizeOf bs

theorem liveEq_symm {rho theta : PactType} (h : LiveEq rho theta) :
    LiveEq theta rho :=
  ⟨h.1.symm, liveEqBody_symm h.2⟩

theorem liveEqBody_trans_fuel : ∀ (n : Nat) (a b c : PactType),
    sizeOf a ≤ n → LiveEqBody a b → LiveEqBody b c → LiveEqBody a c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hSize hab hbc
    have hMA := liveEqBody_messageActions' hab
    have step : ∀ (x y z : PactType), sizeOf x < sizeOf a → LiveEqBody x y →
        LiveEqBody y z → LiveEqBody x z := fun x y z hx hxy hyz =>
      ih (sizeOf x) (lt_of_lt_of_le hx hSize) x y z le_rfl hxy hyz
    have stepBranches : ∀ (bs bs' bs'' : List (BareMessage × PactType)),
        sizeOf bs < sizeOf a → LiveEqBranches bs bs' → LiveEqBranches bs' bs'' →
        LiveEqBranches bs bs'' := by
      intro bs
      induction bs with
      | nil =>
          intro bs' bs'' _ h1 h2
          cases bs' with
          | nil =>
              cases bs'' with
              | nil => simp only [LiveEqBranches]
              | cons _ _ => simp only [LiveEqBranches] at h2
          | cons _ _ => simp only [LiveEqBranches] at h1
      | cons head rest ihRest =>
          intro bs' bs'' hbs h1 h2
          cases bs' with
          | nil => simp only [LiveEqBranches] at h1
          | cons head' rest' =>
              cases bs'' with
              | nil => simp only [LiveEqBranches] at h2
              | cons head'' rest'' =>
                  obtain ⟨action, body⟩ := head
                  obtain ⟨action', body'⟩ := head'
                  obtain ⟨action'', body''⟩ := head''
                  simp only [LiveEqBranches] at h1 h2 ⊢
                  obtain ⟨rfl, hBody1, hRest1⟩ := h1
                  obtain ⟨rfl, hBody2, hRest2⟩ := h2
                  simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hbs
                  exact ⟨rfl, step body body' body'' (by omega) hBody1 hBody2,
                    ihRest rest' rest'' (by omega) hRest1 hRest2⟩
    cases a <;> cases b <;> cases c <;>
      first
        | (simp only [LiveEqBody] at hab; done)
        | (simp only [LiveEqBody] at hbc; done)
        | (simp only [LiveEqBody] at hab hbc ⊢
           obtain ⟨rfl, rfl, hA1⟩ := hab
           obtain ⟨rfl, rfl, hA2⟩ := hbc
           exact ⟨rfl, rfl, hA1.trans hA2⟩)
        | (simp only [LiveEqBody] at hab hbc ⊢; exact hab.trans hbc)
        | (simp only [LiveEqBody]; done)
        | (simp only [LiveEqBody] at hab hbc ⊢
           refine ⟨hab.1.trans (hMA ▸ hbc.1),
             step _ _ _ (by simp only [PactType.choice.sizeOf_spec,
               PactType.seq.sizeOf_spec]; omega) hab.2.1 hbc.2.1,
             step _ _ _ (by simp only [PactType.choice.sizeOf_spec,
               PactType.seq.sizeOf_spec]; omega) hab.2.2 hbc.2.2⟩)
        | (simp only [LiveEqBody] at hab hbc ⊢
           refine ⟨hab.1.trans hbc.1, hab.2.1.trans (hMA ▸ hbc.2.1),
             step _ _ _ (by simp only [PactType.fairChoice.sizeOf_spec,
               PactType.par.sizeOf_spec]; omega) hab.2.2.1 hbc.2.2.1,
             step _ _ _ (by simp only [PactType.fairChoice.sizeOf_spec,
               PactType.par.sizeOf_spec]; omega) hab.2.2.2 hbc.2.2.2⟩)
        | (simp only [LiveEqBody] at hab hbc ⊢
           refine ⟨hab.1.trans hbc.1,
             hab.2.1.trans ((liveEqBody_messageActions' hab.2.2) ▸ hbc.2.1),
             step _ _ _ (by simp only [PactType.recur.sizeOf_spec]; omega)
               hab.2.2 hbc.2.2⟩)
        | (simp only [LiveEqBody] at hab hbc ⊢
           refine ⟨hab.1.trans (hMA ▸ hbc.1),
             step _ _ _ (by simp only [PactType.xoffer.sizeOf_spec,
               PactType.offer.sizeOf_spec]; omega) hab.2.1 hbc.2.1,
             stepBranches _ _ _ (by simp only [PactType.xoffer.sizeOf_spec,
               PactType.offer.sizeOf_spec]; omega) hab.2.2 hbc.2.2⟩)

theorem liveEqBody_trans {a b c : PactType} (hab : LiveEqBody a b)
    (hbc : LiveEqBody b c) : LiveEqBody a c :=
  liveEqBody_trans_fuel (sizeOf a) a b c le_rfl hab hbc

theorem liveEq_trans {a b c : PactType} (hab : LiveEq a b) (hbc : LiveEq b c) :
    LiveEq a c :=
  ⟨hab.1.trans hbc.1, liveEqBody_trans hab.2 hbc.2⟩

/-- A branch head is one of the actions its list records. -/
theorem mem_branchMessageActions_of_mem :
    ∀ {bs : List (BareMessage × PactType)} {action : BareMessage}
      {body : PactType}, (action, body) ∈ bs →
      action ∈ BranchMessageActions bs
  | (a, t) :: rest, action, body, hMem => by
      rw [BranchMessageActions]
      rcases List.mem_cons.mp hMem with hEq | hRest
      · injection hEq with hAction _
        simp [hAction]
      · exact Finset.mem_union_right _
          (mem_branchMessageActions_of_mem hRest)
  termination_by bs => sizeOf bs

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
      case xoffer.xoffer =>
          simp only [LiveEqBody] at hLive
          obtain ⟨hA, he, hbs⟩ := hLive
          rw [MessageActions] at hA
          simp only [typeFutureOffersFuel]
          exact if_congr
            (liveEqBranches_head_gate _ _ _ _ hbs
              (fun act hact => hA act (Finset.mem_union_right _ hact)))
            (branches _ _ _ _ hbs (ih _ _ he)) rfl
      case offer.offer =>
          simp only [LiveEqBody] at hLive
          obtain ⟨hA, he, hbs⟩ := hLive
          rw [MessageActions] at hA
          simp only [typeFutureOffersFuel]
          exact if_congr
            (liveEqBranches_head_gate _ _ _ _ hbs
              (fun act hact => hA act (Finset.mem_union_right _ hact)))
            (branches _ _ _ _ hbs (ih _ _ he)) rfl

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

/-- `FutOff` already agrees under the structural half alone: the outer-alphabet
clause of `LiveEq` is not needed, since both menus can be read at one fuel large
enough for either residual. -/
theorem liveEqBody_preserves_futOff {rho theta : PactType}
    (h : LiveEqBody rho theta) :
    typeFutureOffers rho = typeFutureOffers theta := by
  have hFuel : sizeOf rho + 1 ≤ max (sizeOf rho) (sizeOf theta) + 1 := by
    have := le_max_left (sizeOf rho) (sizeOf theta); omega
  have hFuel' : sizeOf theta + 1 ≤ max (sizeOf rho) (sizeOf theta) + 1 := by
    have := le_max_right (sizeOf rho) (sizeOf theta); omega
  rw [← typeFutureOffersFuel_eq_typeFutureOffers rho _ hFuel,
    ← typeFutureOffersFuel_eq_typeFutureOffers theta _ hFuel']
  exact liveEqBody_futureOffersFuel _ rho theta h

/-- Same-cycle completion agrees on live-equivalent residuals. -/
theorem liveEq_preserves_canComplete {rho theta : PactType} (h : LiveEq rho theta)
    (fuel : Nat) :
    typeCanCompleteThisCycleFuel fuel rho =
      typeCanCompleteThisCycleFuel fuel theta :=
  liveEqBody_canComplete fuel rho theta h.2

end PactType

end Pact
