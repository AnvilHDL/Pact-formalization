import Anvilpp.PactTypes.Syntax.LiveEquivalenceLemmas
import Anvilpp.PactTypes.Syntax.SurvivorAlphabetLemmas
import Anvilpp.PactTypes.Syntax.TypeOffersAlphabet
import Anvilpp.PactTypes.Syntax.TypeTransitionSystemLemmas
import Anvilpp.PactTypes.Syntax.TypeOffersTransitionBridge
import Anvilpp.PactTypes.NewCorrespondence.Helpers.MainHelpers
import Anvilpp.PactTypes.NewCorrespondence.Helpers.OfferAlphabetLemmas
import Anvilpp.PactTypes.NewCorrespondence.Helpers.LiveSubstLemmas
import Anvilpp.PactTypes.NewCorrespondence.Helpers.LiveConjunctiveLemmas

/-!
Live-equivalent residuals take the same decorated steps.
-/

namespace Pact

namespace PactType

/-- Structural inversions.  Only `LiveEqBody` is needed: the outer-alphabet
clause of `LiveEq` does not hold at parallel children, so the induction below
runs on the structural half alone. -/
theorem liveEqBody_message_inv {a : PactTypeAlphabet} {m : MessageId}
    {d : MessageDir} {theta : PactType} (h : LiveEqBody (.message a m d) theta) :
    ∃ b, theta = .message b m d ∧ PactTypeAlphabet.AgreeOn a b {(m, d)} := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case message b m' d' =>
      simp only [LiveEqBody] at h
      obtain ⟨rfl, rfl, hA⟩ := h
      exact ⟨b, rfl, hA⟩

theorem liveEqBody_tock_inv {a : PactTypeAlphabet} {theta : PactType}
    (h : LiveEqBody (.tock a) theta) : ∃ b, theta = .tock b := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case tock b => exact ⟨b, rfl⟩

theorem liveEqBody_skip_inv {a : PactTypeAlphabet} {theta : PactType}
    (h : LiveEqBody (.skip a) theta) : ∃ b, theta = .skip b := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case skip b => exact ⟨b, rfl⟩

theorem liveEqBody_progress_inv {a : PactTypeAlphabet} {pid : ProcId}
    {theta : PactType} (h : LiveEqBody (.progress a pid) theta) :
    ∃ b, theta = .progress b pid := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case progress b pid' =>
      simp only [LiveEqBody] at h
      exact ⟨b, by rw [h]⟩

theorem liveEqBody_choice_inv {a : PactTypeAlphabet} {l r theta : PactType}
    (h : LiveEqBody (.choice a l r) theta) :
    ∃ b l' r', theta = .choice b l' r' ∧ LiveEqBody l l' ∧ LiveEqBody r r' := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case choice b l' r' =>
      simp only [LiveEqBody] at h
      exact ⟨b, l', r', rfl, h.2.1, h.2.2⟩

theorem liveEqBody_fairChoice_inv {a : PactTypeAlphabet} {bid : BranchId}
    {l r theta : PactType} (h : LiveEqBody (.fairChoice a bid l r) theta) :
    ∃ b l' r', theta = .fairChoice b bid l' r' ∧ LiveEqBody l l' ∧
      LiveEqBody r r' := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case fairChoice b bid' l' r' =>
      simp only [LiveEqBody] at h
      obtain ⟨rfl, -, hl, hr⟩ := h
      exact ⟨b, l', r', rfl, hl, hr⟩

theorem liveEqBody_seq_inv {a : PactTypeAlphabet} {l r theta : PactType}
    (h : LiveEqBody (.seq a l r) theta) :
    ∃ b l' r', theta = .seq b l' r' ∧ LiveEqBody l l' ∧ LiveEqBody r r' := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case seq b l' r' =>
      simp only [LiveEqBody] at h
      exact ⟨b, l', r', rfl, h.2.1, h.2.2⟩

theorem liveEqBody_par_inv {a : PactTypeAlphabet} {l r theta : PactType}
    {interface : Interface} (h : LiveEqBody (.par a l r interface) theta) :
    ∃ b l' r', theta = .par b l' r' interface ∧
      PactTypeAlphabet.AgreeOn a b
        (PactType.MessageActions (.par a l r interface)) ∧
      LiveEqBody l l' ∧ LiveEqBody r r' := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case par b l' r' interface' =>
      simp only [LiveEqBody] at h
      obtain ⟨rfl, hA, hl, hr⟩ := h
      exact ⟨b, l', r', rfl, hA, hl, hr⟩

theorem liveEqBody_recur_inv {a : PactTypeAlphabet} {n : String}
    {body theta : PactType} (h : LiveEqBody (.recur a n body) theta) :
    ∃ b body', theta = .recur b n body' ∧
      PactTypeAlphabet.AgreeOn a b (PactType.MessageActions body) ∧
      LiveEqBody body body' := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case recur b n' body' =>
      simp only [LiveEqBody] at h
      obtain ⟨rfl, hA, hb⟩ := h
      exact ⟨b, body', rfl, hA, hb⟩

theorem liveEqBody_xoffer_inv {a : PactTypeAlphabet} {e theta : PactType}
    {bs : List (BareMessage × PactType)}
    (h : LiveEqBody (.xoffer a e bs) theta) :
    ∃ b e' bs', theta = .xoffer b e' bs' ∧
      PactTypeAlphabet.AgreeOn a b (PactType.MessageActions (.xoffer a e bs)) ∧
      LiveEqBody e e' ∧ LiveEqBranches bs bs' := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case xoffer b e' bs' =>
      simp only [LiveEqBody] at h
      exact ⟨b, e', bs', rfl, h.1, h.2.1, h.2.2⟩

theorem liveEqBody_offer_inv {a : PactTypeAlphabet} {e theta : PactType}
    {bs : List (BareMessage × PactType)}
    (h : LiveEqBody (.offer a e bs) theta) :
    ∃ b e' bs', theta = .offer b e' bs' ∧
      PactTypeAlphabet.AgreeOn a b (PactType.MessageActions (.offer a e bs)) ∧
      LiveEqBody e e' ∧ LiveEqBranches bs bs' := by
  cases theta <;> first
    | (exact absurd h (by simp only [LiveEqBody]; exact not_false))
    | skip
  case offer b e' bs' =>
      simp only [LiveEqBody] at h
      exact ⟨b, e', bs', rfl, h.1, h.2.1, h.2.2⟩

/-- Live-equivalent branch lists have the same heads. -/
theorem liveEqBranches_heads :
    ∀ {bs bs' : List (BareMessage × PactType)}, LiveEqBranches bs bs' →
      bs.map Prod.fst = bs'.map Prod.fst
  | [], [], _ => rfl
  | (action, body) :: rest, (action', body') :: rest', h => by
      simp only [LiveEqBranches] at h
      obtain ⟨rfl, -, hRest⟩ := h
      simp only [List.map_cons, liveEqBranches_heads hRest]
  | [], _ :: _, h => by simp only [LiveEqBranches] at h
  | _ :: _, [], h => by simp only [LiveEqBranches] at h
  termination_by bs => sizeOf bs

theorem liveEqBranches_needs {bs bs' : List (BareMessage × PactType)}
    (h : LiveEqBranches bs bs') : typeBranchNeeds bs = typeBranchNeeds bs' := by
  simp only [typeBranchNeeds, List.map_map]
  rw [show (fun branch => typeNeed (Prod.fst branch)) = typeNeed ∘ Prod.fst from
    rfl, ← List.map_map, ← List.map_map, liveEqBranches_heads h]

/-- A branch of one list has a live-equivalent partner with the same head. -/
theorem liveEqBranches_mem :
    ∀ {bs bs' : List (BareMessage × PactType)} {action : BareMessage}
      {body : PactType}, LiveEqBranches bs bs' → (action, body) ∈ bs →
      ∃ body', (action, body') ∈ bs' ∧ LiveEqBody body body'
  | (a, t) :: rest, (a', t') :: rest', action, body, h, hMem => by
      simp only [LiveEqBranches] at h
      obtain ⟨rfl, hBody, hRest⟩ := h
      rcases List.mem_cons.mp hMem with hEq | hRest'
      · injection hEq with hAction hType
        subst hAction; subst hType
        exact ⟨t', by simp, hBody⟩
      · obtain ⟨body', hMem', hLive'⟩ := liveEqBranches_mem hRest hRest'
        exact ⟨body', List.mem_cons_of_mem _ hMem', hLive'⟩
  | [], _, _, _, _, hMem => by simp at hMem
  | (_ :: _), [], _, _, h, _ => by simp only [LiveEqBranches] at h
  termination_by bs => sizeOf bs

theorem liveEqBranches_actions {bs bs' : List (BareMessage × PactType)}
    (h : LiveEqBranches bs bs') : typeBranchActions bs = typeBranchActions bs' := by
  simp only [typeBranchActions, liveEqBranches_heads h]

/-- Inversion at a conjunctive-offer node. -/
theorem liveEq_offer_inv {a : PactTypeAlphabet} {e theta : PactType}
    {bs : List (BareMessage × PactType)}
    (hWF : PactType.AlphabetWellFormed (.offer a e bs))
    (hWFt : theta.AlphabetWellFormed) (h : LiveEq (.offer a e bs) theta) :
    ∃ e' bs', theta = .offer a e' bs' ∧ LiveEq e e' ∧ LiveEqBranches bs bs' := by
  cases theta <;> first
    | (exact absurd h.2 (by simp only [LiveEqBody]; exact not_false))
    | skip
  case offer b e' bs' =>
      obtain ⟨hAlpha, hBody⟩ := h
      simp only [PactType.alphabet] at hAlpha
      subst hAlpha
      simp only [LiveEqBody] at hBody
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      exact ⟨e', bs', rfl, ⟨hWF.2.1.trans hWFt.2.1.symm, hBody.2.1⟩, hBody.2.2⟩

/-- Inversion at an exclusive-offer node. -/
theorem liveEq_xoffer_inv {a : PactTypeAlphabet} {e theta : PactType}
    {bs : List (BareMessage × PactType)}
    (hWF : PactType.AlphabetWellFormed (.xoffer a e bs))
    (hWFt : theta.AlphabetWellFormed) (h : LiveEq (.xoffer a e bs) theta) :
    ∃ e' bs', theta = .xoffer a e' bs' ∧ LiveEq e e' ∧ LiveEqBranches bs bs' := by
  cases theta <;> first
    | (exact absurd h.2 (by simp only [LiveEqBody]; exact not_false))
    | skip
  case xoffer b e' bs' =>
      obtain ⟨hAlpha, hBody⟩ := h
      simp only [PactType.alphabet] at hAlpha
      subst hAlpha
      simp only [LiveEqBody] at hBody
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      exact ⟨e', bs', rfl, ⟨hWF.2.1.trans hWFt.2.1.symm, hBody.2.1⟩, hBody.2.2⟩

/-- Branch bodies of an exclusive offer all carry the node alphabet. -/
theorem branchesAlphabetWellFormed_mem :
    ∀ {a : PactTypeAlphabet} {bs : List (BareMessage × PactType)}
      {action : BareMessage} {body : PactType},
      PactType.BranchesAlphabetWellFormed a bs → (action, body) ∈ bs →
      body.alphabet = a ∧ body.AlphabetWellFormed
  | a, (x, t) :: rest, action, body, hWF, hMem => by
      rw [PactType.BranchesAlphabetWellFormed] at hWF
      rcases List.mem_cons.mp hMem with hEq | hRest
      · injection hEq with hAction hType
        subst hType
        exact ⟨hWF.1, hWF.2.1⟩
      · exact branchesAlphabetWellFormed_mem hWF.2.2 hRest
  | _, [], _, _, _, hMem => by simp at hMem
  termination_by _ bs => sizeOf bs

/-- Substitution adds only the replacement's own actions. -/
theorem messageActions_replaceVar_subset (n : String) (R : PactType) :
    ∀ (k : Nat) (b : PactType), sizeOf b ≤ k →
      PactType.MessageActions (b.replaceVar n R) ⊆
        PactType.MessageActions b ∪ PactType.MessageActions R := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have step : ∀ (x : PactType), sizeOf x < k →
        PactType.MessageActions (x.replaceVar n R) ⊆
          PactType.MessageActions x ∪ PactType.MessageActions R :=
      fun x hx => ih (sizeOf x) hx x le_rfl
    have branches : ∀ (bs : List (BareMessage × PactType)), sizeOf bs < k →
        PactType.BranchMessageActions (PactType.replaceBranches bs n R) ⊆
          PactType.BranchMessageActions bs ∪ PactType.MessageActions R := by
      intro bs
      induction bs with
      | nil => intro _; simp [PactType.replaceBranches,
          PactType.BranchMessageActions]
      | cons head rest ihRest =>
          intro hSize
          obtain ⟨action, body⟩ := head
          simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
          simp only [PactType.replaceBranches, PactType.BranchMessageActions]
          refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
          · exact fun x hx => Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
          · intro x hx
            rcases Finset.mem_union.mp (step body (by omega) hx) with h | h
            · exact Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ h))
            · exact Finset.mem_union_right _ h
          · intro x hx
            rcases Finset.mem_union.mp (ihRest (by omega) hx) with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
            · exact Finset.mem_union_right _ h
    intro b hSize
    cases b with
    | message _ _ _ | progress _ _ | tock _ | skip _ =>
        simp [PactType.replaceVar, PactType.MessageActions]
    | var a other =>
        simp only [PactType.replaceVar]
        by_cases hEq : n = other
        · rw [if_pos hEq]; exact Finset.subset_union_right
        · rw [if_neg hEq]; simp [PactType.MessageActions]
    | choice a l r | seq a l r | fairChoice a _ l r | par a l r _ =>
        simp only [PactType.choice.sizeOf_spec, PactType.seq.sizeOf_spec,
          PactType.fairChoice.sizeOf_spec, PactType.par.sizeOf_spec] at hSize
        simp only [PactType.replaceVar, PactType.MessageActions]
        refine Finset.union_subset (fun x hx => ?_) (fun x hx => ?_)
        · rcases Finset.mem_union.mp (step l (by omega) hx) with h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · exact Finset.mem_union_right _ h
        · rcases Finset.mem_union.mp (step r (by omega) hx) with h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
          · exact Finset.mem_union_right _ h
    | recur a other body =>
        simp only [PactType.recur.sizeOf_spec] at hSize
        simp only [PactType.replaceVar]
        by_cases hEq : n = other
        · rw [if_pos hEq]; exact Finset.subset_union_left
        · rw [if_neg hEq]
          simp only [PactType.MessageActions]
          exact step body (by omega)
    | xoffer a e bs | offer a e bs =>
        simp only [PactType.xoffer.sizeOf_spec, PactType.offer.sizeOf_spec]
          at hSize
        simp only [PactType.replaceVar, PactType.MessageActions]
        refine Finset.union_subset (fun x hx => ?_) (fun x hx => ?_)
        · rcases Finset.mem_union.mp (step e (by omega) hx) with h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · exact Finset.mem_union_right _ h
        · rcases Finset.mem_union.mp (branches bs (by omega) hx) with h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
          · exact Finset.mem_union_right _ h

theorem messageActions_replaceVar_subset' (n : String) (R b : PactType) :
    PactType.MessageActions (b.replaceVar n R) ⊆
      PactType.MessageActions b ∪ PactType.MessageActions R :=
  messageActions_replaceVar_subset n R (sizeOf b) b le_rfl

/-- A step introduces no new message action.  Live equivalence indexes its
per-node agreement on the actions the body still uses, so that set must not grow
when the residual advances. -/
theorem typeOffers_messageActions_subset :
    ∀ {env : TypeEnvironment} {rho : PactType} {label : TypeLabel}
      {rho' : PactType} {current future : Finset BareMessage},
      TypeOffers env rho label rho' current future →
      PactType.MessageActions rho' ⊆ PactType.MessageActions rho := by
  intro env rho label rho' current future hOffers
  induction hOffers with
  | action | progress | cycle => simp [PactType.MessageActions]
  | action_wait | cycle_wait | skip => exact Finset.Subset.refl _
  | choice_left | fair_left =>
      simp only [PactType.MessageActions]; exact Finset.subset_union_left
  | choice_right | fair_right =>
      simp only [PactType.MessageActions]; exact Finset.subset_union_right
  | recur env alphabet name body _ =>
      simp only [PactType.MessageActions]
      intro x hx
      rcases Finset.mem_union.mp
        (messageActions_replaceVar_subset' name _ body hx) with h | h
      · exact h
      · simpa only [PactType.MessageActions] using h
  | seq _ _ _ _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.MessageActions]
      exact Finset.union_subset_union ih (Finset.Subset.refl _)
  | seq_tock _ _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.MessageActions]
      exact Finset.union_subset_union ih (Finset.Subset.refl _)
  | seq_fuse | seq_fuse_tock =>
      simp only [PactType.MessageActions]; exact Finset.subset_union_right
  | xoffer_branch env alphabet elseType branches action processType hConds _ =>
      simp only [PactType.MessageActions]
      intro x hx
      exact Finset.mem_union_right _
        (branch_subset_branchMessageActions hConds.2.1
          (Finset.mem_union_right _ hx))
  | xoffer_else | offer_else =>
      simp only [PactType.MessageActions]; exact Finset.subset_union_left
  | xoffer_wait | offer_wait => exact Finset.Subset.refl _
  | offer_some env alphabet elseType branches enabled _ _ =>
      rw [parallelTypeBranchesSelecting_messageActions]
      simp only [PactType.MessageActions]
      exact Finset.subset_union_right
  | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihL ihR =>
      simp only [PactType.MessageActions]
      exact Finset.union_subset_union ihL ihR
  | par_fuse | par_fuse_tock => simp [PactType.MessageActions]
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [(PactType.reannotate_ownership_data _ _).2.1]
      simp only [PactType.MessageActions]
      exact Finset.Subset.trans ih Finset.subset_union_right
  | left_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [(PactType.reannotate_ownership_data _ _).2.1]
      simp only [PactType.MessageActions]
      exact Finset.Subset.trans ih Finset.subset_union_right
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [(PactType.reannotate_ownership_data _ _).2.1]
      simp only [PactType.MessageActions]
      exact Finset.Subset.trans ih Finset.subset_union_left
  | right_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [(PactType.reannotate_ownership_data _ _).2.1]
      simp only [PactType.MessageActions]
      exact Finset.Subset.trans ih Finset.subset_union_left

/-- The per-node agreement carried by live equivalence, read off at the node
itself.  Atomic nodes use no action, so their clause carries none. -/
theorem liveEqBody_agreeOn {x y : PactType} (h : LiveEqBody x y) :
    PactTypeAlphabet.AgreeOn x.alphabet y.alphabet
      (PactType.MessageActions x) := by
  cases x <;> cases y <;>
    first
      | (simp only [LiveEqBody] at h; done)
      | (intro action hAction; simp [PactType.MessageActions] at hAction; done)
      | (simp only [LiveEqBody] at h
         obtain ⟨rfl, rfl, hA⟩ := h
         simpa only [PactType.MessageActions, PactType.alphabet] using hA)
      | (simp only [LiveEqBody] at h
         simpa only [PactType.alphabet] using h.1)
      | (simp only [LiveEqBody] at h
         simpa only [PactType.alphabet] using h.2.1)
      | (simp only [LiveEqBody] at h
         simpa only [PactType.alphabet, PactType.MessageActions] using h.2.1)

theorem typeBranchActions_subset_branchMessageActions
    (bs : List (BareMessage × PactType)) :
    typeBranchActions bs ⊆ PactType.BranchMessageActions bs := by
  classical
  intro x hx
  simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hx
  obtain ⟨branch, hBranch, rfl⟩ := hx
  exact mem_branchMessageActions_of_mem (body := branch.2) (by simpa using hBranch)


/-- A step's current offer only mentions actions its source uses. -/
theorem typeOffers_current_subset :
    ∀ {env : TypeEnvironment} {rho : PactType} {label : TypeLabel}
      {rho' : PactType} {current future : Finset BareMessage},
      TypeOffers env rho label rho' current future →
      current ⊆ PactType.MessageActions rho := by
  intro env rho label rho' current future hOffers
  induction hOffers with
  | action | action_wait => simp [PactType.MessageActions]
  | cycle | cycle_wait | skip | progress | recur | choice_left | choice_right
  | fair_left | fair_right | offer_some => simp
  | seq _ _ _ _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.MessageActions]
      exact Finset.Subset.trans ih Finset.subset_union_left
  | seq_tock => simp
  | seq_fuse _ _ _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.MessageActions]
      exact Finset.Subset.trans ih Finset.subset_union_left
  | seq_fuse_tock => simp
  | xoffer_branch env alphabet elseType branches action processType hConds _ =>
      simp only [PactType.MessageActions]
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_union_right _
        (mem_branchMessageActions_of_mem (body := processType) hConds.2.1)
  | xoffer_else => simp
  | xoffer_wait env alphabet elseType branches _ _ =>
      simp only [PactType.MessageActions, typeWaitingOffers]
      intro x hx
      exact Finset.mem_union_right _
        (typeBranchActions_subset_branchMessageActions branches
          (Finset.mem_inter.mp hx).2)
  | offer_else env alphabet elseType branches _ _
  | offer_wait env alphabet elseType branches _ _ =>
      simp only [PactType.MessageActions]
      intro x hx
      exact Finset.mem_union_right _
        (typeBranchActions_subset_branchMessageActions branches hx)
  | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihL ihR =>
      simp only [PactType.MessageActions, hideTypeOffers]
      intro x hx
      rcases Finset.mem_union.mp (Finset.mem_filter.mp hx).1 with h | h
      · exact Finset.mem_union_left _ (ihL h)
      · exact Finset.mem_union_right _ (ihR h)
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihL ihR =>
      simp only [PactType.MessageActions, hideTypeOffers]
      intro x hx
      rcases Finset.mem_union.mp (Finset.mem_filter.mp hx).1 with h | h
      · exact Finset.mem_union_left _ (ihL h)
      · exact Finset.mem_union_right _ (ihR h)
  | par_fuse_tock => simp
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.MessageActions, hideTypeOffers]
      intro x hx
      exact Finset.mem_union_right _ (ih (Finset.mem_filter.mp hx).1)
  | left_complete_tock => simp
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.MessageActions, hideTypeOffers]
      intro x hx
      exact Finset.mem_union_left _ (ih (Finset.mem_filter.mp hx).1)
  | right_complete_tock => simp

/-! ### Transporting a parallel child's local environment -/

theorem typeNeed_typeNeed (a : BareMessage) : typeNeed (typeNeed a) = a := by
  obtain ⟨m, d⟩ := a
  cases d <;> simp [typeNeed, MessageDir.invert]


theorem typeNeed_injective {a b : BareMessage} (h : typeNeed a = typeNeed b) :
    a = b := by
  have := congrArg typeNeed h
  rwa [typeNeed_typeNeed, typeNeed_typeNeed] at this

theorem mem_project_typeNeed {alphabet : PactTypeAlphabet}
    {offers : Finset BareMessage} {action : BareMessage} :
    typeNeed action ∈ projectTypeEnvironmentOffers alphabet offers ↔
      (typeNeed action ∈ offers ∧ action ∈ alphabet.actions) := by
  classical
  simp only [projectTypeEnvironmentOffers, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hOffer, x, hx, hEq⟩
    exact ⟨hOffer, typeNeed_injective hEq ▸ hx⟩
  · rintro ⟨hOffer, hAction⟩
    exact ⟨hOffer, action, hAction, rfl⟩

/-- One child's local environment, re-projected onto a live-equivalent child's
alphabet, is an environment that child cannot tell apart. -/
theorem localEnvAgree {l l' : PactType} {current current' : Finset BareMessage}
    (hAgree : PactTypeAlphabet.AgreeOn l.alphabet l'.alphabet
      (PactType.MessageActions l))
    (hOffers : ∀ action ∈ PactType.MessageActions l,
      (typeNeed action ∈ current ↔ typeNeed action ∈ current')) :
    ∀ action ∈ PactType.MessageActions l,
      (typeNeed action ∈
          projectTypeEnvironmentOffers l.alphabet current ↔
        typeNeed action ∈
          projectTypeEnvironmentOffers l'.alphabet current') := by
  intro action hAction
  simp only [mem_project_typeNeed]
  exact and_congr (hOffers action hAction) (hAgree action hAction)

/-- Both parallel children's local environments transport together: the two
premises of the parallel rule are cross-linked, so they are rebuilt as a pair. -/
theorem parLocalEnvs_transport
    {outer outer' leftEnv rightEnv : TypeEnvironment} {interface : Interface}
    {l r l' r' : PactType} {lc lf rc rf : Finset BareMessage}
    (hL : LocalTypeOfferEnvironment outer interface l rightEnv rc rf leftEnv)
    (hR : LocalTypeOfferEnvironment outer interface r leftEnv lc lf rightEnv)
    (hOuter : TypeEnvironment.AgreeOnNeeds outer outer'
      (PactType.MessageActions l ∪ PactType.MessageActions r))
    (hAgreeL : PactTypeAlphabet.AgreeOn l.alphabet l'.alphabet
      (PactType.MessageActions l))
    (hAgreeR : PactTypeAlphabet.AgreeOn r.alphabet r'.alphabet
      (PactType.MessageActions r)) :
    ∃ leftEnv' rightEnv',
      LocalTypeOfferEnvironment outer' interface l' rightEnv' rc rf leftEnv' ∧
      LocalTypeOfferEnvironment outer' interface r' leftEnv' lc lf rightEnv' ∧
      TypeEnvironment.AgreeOnNeeds leftEnv leftEnv'
        (PactType.MessageActions l) ∧
      TypeEnvironment.AgreeOnNeeds rightEnv rightEnv'
        (PactType.MessageActions r) := by
  classical
  cases hL with
  | clock _ _ _ _ hClock =>
      cases hR with
      | clock _ _ _ _ _ =>
          exact ⟨TypeEnvironment.tock, TypeEnvironment.tock,
            LocalTypeOfferEnvironment.clock outer' interface l' rc rf
              (by rw [← hOuter.1]; exact hClock),
            LocalTypeOfferEnvironment.clock outer' interface r' lc lf
              (by rw [← hOuter.1]; exact hClock),
            TypeEnvironment.AgreeOnNeeds.refl _ _,
            TypeEnvironment.AgreeOnNeeds.refl _ _⟩
      | ordinary _ _ _ _ _ _ hOuterClock _ _ _ _ =>
          exact absurd hClock (by rw [hOuterClock]; simp)
  | ordinary _ _ _ _ _ _ hOuterClock hSibClockL hLocalClockL hImmL hFutL =>
      cases hR with
      | clock _ _ _ _ hClock => exact absurd hClock (by rw [hOuterClock]; simp)
      | ordinary _ _ _ _ _ _ _ hSibClockR hLocalClockR hImmR hFutR =>
          refine ⟨TypeEnvironment.mk
              (projectTypeEnvironmentOffers l'.alphabet outer'.immediate ∪
                restrictTypeOffers interface rc)
              ((projectTypeEnvironmentOffers l'.alphabet outer'.future ∪
                restrictTypeOffers interface rf) \
                (projectTypeEnvironmentOffers l'.alphabet outer'.immediate ∪
                  restrictTypeOffers interface rc))
              false,
            TypeEnvironment.mk
              (projectTypeEnvironmentOffers r'.alphabet outer'.immediate ∪
                restrictTypeOffers interface lc)
              ((projectTypeEnvironmentOffers r'.alphabet outer'.future ∪
                restrictTypeOffers interface lf) \
                (projectTypeEnvironmentOffers r'.alphabet outer'.immediate ∪
                  restrictTypeOffers interface lc))
              false,
            LocalTypeOfferEnvironment.ordinary outer' _ _ interface l' rc rf
              (by rw [← hOuter.1]; exact hOuterClock) rfl rfl rfl rfl,
            LocalTypeOfferEnvironment.ordinary outer' _ _ interface r' lc lf
              (by rw [← hOuter.1]; exact hOuterClock) rfl rfl rfl rfl, ?_, ?_⟩
          · refine ⟨by rw [hLocalClockL], ?_, ?_⟩
            · intro action hAction
              rw [hImmL]
              simp only [Finset.mem_union]
              exact or_congr_left (localEnvAgree hAgreeL (fun x hx => hOuter.2.1 x (Finset.mem_union_left _ hx)) action hAction)
            · intro action hAction
              rw [hFutL, hImmL]
              simp only [Finset.mem_sdiff, Finset.mem_union]
              exact and_congr
                (or_congr_left (localEnvAgree hAgreeL (fun x hx => hOuter.2.2 x (Finset.mem_union_left _ hx)) action hAction))
                (not_congr (or_congr_left
                  (localEnvAgree hAgreeL (fun x hx => hOuter.2.1 x (Finset.mem_union_left _ hx)) action hAction)))
          · refine ⟨by rw [hLocalClockR], ?_, ?_⟩
            · intro action hAction
              rw [hImmR]
              simp only [Finset.mem_union]
              exact or_congr_left (localEnvAgree hAgreeR (fun x hx => hOuter.2.1 x (Finset.mem_union_right _ hx)) action hAction)
            · intro action hAction
              rw [hFutR, hImmR]
              simp only [Finset.mem_sdiff, Finset.mem_union]
              exact and_congr
                (or_congr_left (localEnvAgree hAgreeR (fun x hx => hOuter.2.2 x (Finset.mem_union_right _ hx)) action hAction))
                (not_congr (or_congr_left
                  (localEnvAgree hAgreeR (fun x hx => hOuter.2.1 x (Finset.mem_union_right _ hx)) action hAction)))

/-- The completed side offers no menu, so the survivor's local environment
transports on its own: only the outer environment and the child alphabet move. -/
theorem localEnv_transport_solo
    {outer outer' localEnv : TypeEnvironment} {interface : Interface}
    {l l' : PactType}
    (hLocal : LocalTypeOfferEnvironment outer interface l localEnv ∅ ∅ localEnv)
    (hOuter : TypeEnvironment.AgreeOnNeeds outer outer'
      (PactType.MessageActions l))
    (hAgree : PactTypeAlphabet.AgreeOn l.alphabet l'.alphabet
      (PactType.MessageActions l)) :
    ∃ localEnv',
      LocalTypeOfferEnvironment outer' interface l' localEnv' ∅ ∅ localEnv' ∧
      TypeEnvironment.AgreeOnNeeds localEnv localEnv'
        (PactType.MessageActions l) := by
  classical
  cases hLocal with
  | clock _ _ _ _ hClock =>
      exact ⟨TypeEnvironment.tock,
        LocalTypeOfferEnvironment.clock outer' interface l' ∅ ∅
          (by rw [← hOuter.1]; exact hClock),
        TypeEnvironment.AgreeOnNeeds.refl _ _⟩
  | ordinary _ _ _ _ _ _ hOuterClock hSibClock hLocalClock hImm hFut =>
      refine ⟨TypeEnvironment.mk
          (projectTypeEnvironmentOffers l'.alphabet outer'.immediate ∪
            restrictTypeOffers interface ∅)
          ((projectTypeEnvironmentOffers l'.alphabet outer'.future ∪
            restrictTypeOffers interface ∅) \
            (projectTypeEnvironmentOffers l'.alphabet outer'.immediate ∪
              restrictTypeOffers interface ∅))
          false,
        LocalTypeOfferEnvironment.ordinary outer' _ _ interface l' ∅ ∅
          (by rw [← hOuter.1]; exact hOuterClock) rfl rfl rfl rfl, ?_⟩
      refine ⟨by rw [hLocalClock], ?_, ?_⟩
      · intro action hAction
        rw [hImm]
        simp only [Finset.mem_union]
        exact or_congr_left
          (localEnvAgree hAgree (fun x hx => hOuter.2.1 x hx) action hAction)
      · intro action hAction
        rw [hFut, hImm]
        simp only [Finset.mem_sdiff, Finset.mem_union]
        exact and_congr
          (or_congr_left
            (localEnvAgree hAgree (fun x hx => hOuter.2.2 x hx) action hAction))
          (not_congr (or_congr_left
            (localEnvAgree hAgree (fun x hx => hOuter.2.1 x hx) action hAction)))

/-- A parallel child's local environment is well formed for that child: the
projected part is inside its alphabet by construction, and the sibling's
interface offers land there because complementarity declares their complements. -/
theorem localEnv_wellFormed_interface
    {outer sib localEnv : TypeEnvironment} {interface : Interface}
    {l sibling : PactType} {c f : Finset BareMessage}
    (hLocal : LocalTypeOfferEnvironment outer interface l sib c f localEnv)
    (hComp : PactTypeAlphabet.ComplementaryOn l.alphabet sibling.alphabet
      interface)
    (hOneL : l.alphabet.WellFormed) (hOne : sibling.alphabet.WellFormed)
    (hCurrent : outer.clock = false → ∀ x ∈ c, x.1 ∈ interface →
      x ∈ sibling.alphabet.actions)
    (hFuture : outer.clock = false → ∀ x ∈ f, x.1 ∈ interface →
      x ∈ sibling.alphabet.actions) :
    localEnv.WellFormed l.alphabet := by
  classical
  have hProject : ∀ (offers : Finset BareMessage),
      ∀ x ∈ projectTypeEnvironmentOffers l.alphabet offers,
        x ∈ l.alphabet.actions.image typeNeed := by
    intro offers x hx
    simp only [projectTypeEnvironmentOffers, Finset.mem_filter] at hx
    exact hx.2
  cases hLocal with
  | clock =>
      refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ => by simp [TypeEnvironment.tock],
        by simp [TypeEnvironment.tock], by simp [TypeEnvironment.tock]⟩
  | ordinary _ _ _ _ _ _ hOuterClock _ hLocalClock hImm hFut =>
      have hRestrict : ∀ (offers : Finset BareMessage),
          (∀ x ∈ offers, x.1 ∈ interface → x ∈ sibling.alphabet.actions) →
          ∀ x ∈ restrictTypeOffers interface offers,
            x ∈ l.alphabet.actions.image typeNeed := by
        intro offers hSub x hx
        simp only [restrictTypeOffers, Finset.mem_filter] at hx
        exact Finset.mem_image.mpr ⟨typeNeed x,
          complement_declared_of_offered hComp hOneL hOne
            (hSub x hx.1 hx.2) hx.2,
          typeNeed_typeNeed x⟩
      refine ⟨fun hClock => absurd (hClock.symm.trans hLocalClock) (by simp),
        fun _ => ?_, ?_, ?_⟩
      · rw [hFut]; exact Finset.inter_sdiff_self _ _
      · rw [hImm]
        exact Finset.union_subset (hProject _)
          (hRestrict _ (hCurrent hOuterClock))
      · rw [hFut]
        exact Finset.Subset.trans Finset.sdiff_subset
          (Finset.union_subset (hProject _)
            (hRestrict _ (hFuture hOuterClock)))

/-- Offers inside the sibling's whole alphabet are in particular inside it on
the interface. -/
theorem localEnv_wellFormed
    {outer sib localEnv : TypeEnvironment} {interface : Interface}
    {l sibling : PactType} {c f : Finset BareMessage}
    (hLocal : LocalTypeOfferEnvironment outer interface l sib c f localEnv)
    (hComp : PactTypeAlphabet.ComplementaryOn l.alphabet sibling.alphabet
      interface)
    (hOneL : l.alphabet.WellFormed) (hOne : sibling.alphabet.WellFormed)
    (hCurrent : c ⊆ sibling.alphabet.actions)
    (hFuture : f ⊆ sibling.alphabet.actions) :
    localEnv.WellFormed l.alphabet :=
  localEnv_wellFormed_interface hLocal hComp hOneL hOne
    (fun _ _ hx _ => hCurrent hx) (fun _ _ hx _ => hFuture hx)

/-! ### The offer side conditions read branch heads only, so they transport -/

theorem mem_typeBranchNeeds_iff {bs : List (BareMessage × PactType)}
    {x : BareMessage} :
    x ∈ typeBranchNeeds bs ↔ ∃ a ∈ typeBranchActions bs, typeNeed a = x := by
  simp only [typeBranchNeeds, typeBranchActions, List.mem_toFinset,
    List.mem_map]
  constructor
  · rintro ⟨branch, hBranch, rfl⟩
    exact ⟨branch.1, ⟨branch, hBranch, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨branch, hBranch, rfl⟩, rfl⟩
    exact ⟨branch, hBranch, rfl⟩

theorem typeResolved_transport {env env' : TypeEnvironment}
    {bs : List (BareMessage × PactType)} {used : Finset BareMessage}
    (hAgree : TypeEnvironment.AgreeOnNeeds env env' used)
    (hSub : typeBranchActions bs ⊆ used) (h : TypeResolved env bs) :
    TypeResolved env' bs := by
  classical
  simp only [TypeResolved, Finset.eq_empty_iff_forall_notMem,
    Finset.mem_inter] at h ⊢
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_typeBranchNeeds_iff.mp hx.1
  exact h _ ⟨hx.1, (hAgree.2.2 a (hSub ha)).mpr hx.2⟩

theorem typeNoImmediateBranch_transport {env env' : TypeEnvironment}
    {bs : List (BareMessage × PactType)} {used : Finset BareMessage}
    (hAgree : TypeEnvironment.AgreeOnNeeds env env' used)
    (hSub : typeBranchActions bs ⊆ used) (h : TypeNoImmediateBranch env bs) :
    TypeNoImmediateBranch env' bs := by
  classical
  simp only [TypeNoImmediateBranch, Finset.eq_empty_iff_forall_notMem,
    Finset.mem_inter] at h ⊢
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_typeBranchNeeds_iff.mp hx.1
  exact h _ ⟨hx.1, (hAgree.2.1 a (hSub ha)).mpr hx.2⟩

theorem typeResolved_not_transport {env env' : TypeEnvironment}
    {bs : List (BareMessage × PactType)} {used : Finset BareMessage}
    (hAgree : TypeEnvironment.AgreeOnNeeds env env' used)
    (hSub : typeBranchActions bs ⊆ used) (h : ¬ TypeResolved env bs) :
    ¬ TypeResolved env' bs :=
  fun hRes => h (typeResolved_transport hAgree.symm hSub hRes)

theorem typeWaitingOffers_transport {env env' : TypeEnvironment}
    {bs : List (BareMessage × PactType)} {used : Finset BareMessage}
    (hAgree : TypeEnvironment.AgreeOnNeeds env env' used)
    (hSub : typeBranchActions bs ⊆ used) :
    typeWaitingOffers env bs = typeWaitingOffers env' bs := by
  classical
  apply Finset.ext
  intro x
  simp only [typeWaitingOffers, Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨⟨f, hf, rfl⟩, hAct⟩
    refine ⟨⟨typeNeed (typeNeed f), ?_, by rw [typeNeed_typeNeed]⟩, hAct⟩
    have hBack := (hAgree.2.2 (typeNeed f)
      (hSub (by simpa [typeNeed_typeNeed] using hAct))).mp
    rw [typeNeed_typeNeed] at hBack ⊢
    exact hBack hf
  · rintro ⟨⟨f, hf, rfl⟩, hAct⟩
    refine ⟨⟨typeNeed (typeNeed f), ?_, by rw [typeNeed_typeNeed]⟩, hAct⟩
    have hBack := (hAgree.2.2 (typeNeed f)
      (hSub (by simpa [typeNeed_typeNeed] using hAct))).mpr
    rw [typeNeed_typeNeed] at hBack ⊢
    exact hBack hf

/-! ### The syntactic future menu stays inside the source's own actions -/

/-- A future menu only advertises actions the syntax it comes from performs. -/
theorem typeFutureOffersFuel_subset_messageActions :
    ∀ fuel processType,
      typeFutureOffersFuel fuel processType ⊆ processType.MessageActions := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType
      simp [typeFutureOffersFuel]
  | succ fuel ih =>
      intro processType
      cases processType with
      | message alphabet msg dir =>
          by_cases hDeclared : (msg, dir) ∈ alphabet.actions <;>
            simp [typeFutureOffersFuel, PactType.MessageActions, hDeclared]
      | progress alphabet pid =>
          simp [typeFutureOffersFuel, PactType.MessageActions]
      | tock alphabet =>
          simp [typeFutureOffersFuel, PactType.MessageActions]
      | skip alphabet =>
          simp [typeFutureOffersFuel, PactType.MessageActions]
      | var alphabet name =>
          simp [typeFutureOffersFuel, PactType.MessageActions]
      | recur alphabet name body =>
          simpa [typeFutureOffersFuel, PactType.MessageActions] using ih body
      | choice alphabet left right | fairChoice alphabet _ left right =>
          simpa [typeFutureOffersFuel, PactType.MessageActions] using
            Finset.union_subset_union (ih left) (ih right)
      | seq alphabet left right =>
          simp only [typeFutureOffersFuel, PactType.MessageActions]
          split
          · exact Finset.union_subset_union (ih left) (ih right)
          · exact (ih left).trans Finset.subset_union_left
      | par alphabet left right interface =>
          intro action hAction
          simp only [typeFutureOffersFuel, hideTypeOffers,
            Finset.mem_filter, Finset.mem_union, PactType.MessageActions] at hAction ⊢
          rcases hAction.1 with hLeft | hRight
          · exact Or.inl (ih left hLeft)
          · exact Or.inr (ih right hRight)
      | xoffer alphabet elseType branches | offer alphabet elseType branches =>
          simp only [typeFutureOffersFuel, PactType.MessageActions]
          have hHeadSubsetAll : ∀ (bs : List (BareMessage × PactType))
              branch, branch ∈ bs →
                {branch.1} ⊆ PactType.BranchMessageActions bs := by
            intro bs
            induction bs with
            | nil =>
                intro branch hBranch
                cases hBranch
            | cons head rest restIH =>
                intro branch hBranch
                simp only [List.mem_cons] at hBranch
                rw [PactType.BranchMessageActions.eq_def]
                rcases hBranch with rfl | hBranch
                · exact Finset.subset_union_left.trans Finset.subset_union_left
                · exact (restIH branch hBranch).trans Finset.subset_union_right
          have hBodySubsetAll : ∀ (bs : List (BareMessage × PactType))
              branch, branch ∈ bs →
                branch.2.MessageActions ⊆
                  PactType.BranchMessageActions bs := by
            intro bs
            induction bs with
            | nil =>
                intro branch hBranch
                cases hBranch
            | cons head rest restIH =>
                intro branch hBranch
                simp only [List.mem_cons] at hBranch
                rw [PactType.BranchMessageActions.eq_def]
                rcases hBranch with rfl | hBranch
                · intro action hAction
                  exact Finset.mem_union.mpr
                    (Or.inl (Finset.mem_union.mpr (Or.inr hAction)))
                · exact (restIH branch hBranch).trans Finset.subset_union_right
          have hFold : ∀ (rest : List (BareMessage × PactType)) initial,
              initial ⊆ elseType.MessageActions ∪
                  PactType.BranchMessageActions branches →
              (∀ branch ∈ rest, branch ∈ branches) →
              rest.foldl (fun offers branch =>
                  offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
                  initial ⊆
                elseType.MessageActions ∪
                  PactType.BranchMessageActions branches := by
            intro rest
            induction rest with
            | nil =>
                intro initial hInitial _
                simpa using hInitial
            | cons branch tail tailIH =>
                intro initial hInitial hRest
                apply tailIH
                · apply Finset.union_subset
                  · apply Finset.union_subset
                    · exact hInitial
                    · intro action hAction
                      have hBranch : branch ∈ branches := hRest branch (by simp)
                      exact Finset.mem_union.mpr
                        (Or.inr (hHeadSubsetAll branches branch hBranch hAction))
                  · intro action hAction
                    have hBranch : branch ∈ branches := hRest branch (by simp)
                    have hInBranch : action ∈ branch.2.MessageActions :=
                      ih branch.2 hAction
                    exact Finset.mem_union.mpr
                      (Or.inr (hBodySubsetAll branches branch hBranch hInBranch))
                · intro other hOther
                  exact hRest other (by simp [hOther])
          split
          · apply hFold branches (typeFutureOffersFuel fuel elseType)
            · exact (ih elseType).trans Finset.subset_union_left
            · simp
          · simp

/-- Fuel-free form of `typeFutureOffersFuel_subset_messageActions`. -/
theorem typeFutureOffers_subset_messageActions (processType : PactType) :
    typeFutureOffers processType ⊆ processType.MessageActions :=
  typeFutureOffersFuel_subset_messageActions _ processType

/-- A step is offered only to an environment well formed for its source. -/
theorem typeOffers_env_wellFormed :
    ∀ {env : TypeEnvironment} {rho : PactType} {label : TypeLabel}
      {rho' : PactType} {current future : Finset BareMessage},
      TypeOffers env rho label rho' current future →
      rho.AlphabetWellFormed → env.WellFormed rho.alphabet := by
  intro env rho label rho' current future hOffers
  induction hOffers with
  | seq _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro hWF
      simp only [PactType.AlphabetWellFormed] at hWF
      have h := ih hWF.2.2.2.1
      rw [hWF.2.1] at h
      exact h
  | seq_tock _ _ _ _ _ _ _ _ _ ih =>
      intro hWF
      simp only [PactType.AlphabetWellFormed] at hWF
      have h := ih hWF.2.2.2.1
      rw [hWF.2.1] at h
      exact h
  | seq_fuse _ _ _ _ _ _ _ _ _ _ ih =>
      intro hWF
      simp only [PactType.AlphabetWellFormed] at hWF
      have h := ih hWF.2.2.2.1
      rw [hWF.2.1] at h
      exact h
  | seq_fuse_tock _ _ _ _ _ _ _ _ ih =>
      intro hWF
      simp only [PactType.AlphabetWellFormed] at hWF
      have h := ih hWF.2.2.2.1
      rw [hWF.2.1] at h
      exact h
  | _ =>
      intro _
      simp only [PactType.alphabet]
      tauto

/-- A step's future offer only mentions actions its source uses. -/
theorem typeOffers_future_subset_messageActions
    {env : TypeEnvironment} {rho : PactType} {label : TypeLabel}
    {rho' : PactType} {current future : Finset BareMessage}
    (hOffers : TypeOffers env rho label rho' current future) :
    future ⊆ PactType.MessageActions rho := by
  intro action hAction
  rcases Finset.mem_union.mp
    (typeOffers_future_subset_target_union_current hOffers hAction) with h | h
  · exact typeOffers_messageActions_subset hOffers
      (typeFutureOffers_subset_messageActions rho' h)
  · exact typeOffers_current_subset hOffers h

/-- An interface action a sibling still offers is declared by that sibling: the
local environment carries its complement, and one polarity of each interface id
is declared on each side. -/
theorem sibling_offer_declared
    {outer sib localEnv : TypeEnvironment} {interface : Interface}
    {l sibling : PactType} {c f : Finset BareMessage} {x : BareMessage}
    (hLocal : LocalTypeOfferEnvironment outer interface l sib c f localEnv)
    (hLocalWF : localEnv.WellFormed l.alphabet)
    (hComp : PactTypeAlphabet.ComplementaryOn l.alphabet sibling.alphabet
      interface)
    (hOneL : l.alphabet.WellFormed) (hClock : outer.clock = false)
    (hMem : x ∈ c ∪ f) (hIface : x.1 ∈ interface) :
    x ∈ sibling.alphabet.actions := by
  classical
  have hNeed : typeNeed x ∈ l.alphabet.actions := by
    cases hLocal with
    | clock _ _ _ _ hClockTrue =>
        rw [hClockTrue] at hClock
        exact absurd hClock (by simp)
    | ordinary _ _ _ _ _ _ _ _ _ hImm hFut =>
        have hInEnv : x ∈ localEnv.immediate ∪ localEnv.future := by
          rcases Finset.mem_union.mp hMem with h | h
          · refine Finset.mem_union_left _ ?_
            rw [hImm]
            refine Finset.mem_union_right _ ?_
            simp only [restrictTypeOffers, Finset.mem_filter]
            exact ⟨h, hIface⟩
          · by_cases hImmMem : x ∈ localEnv.immediate
            · exact Finset.mem_union_left _ hImmMem
            · refine Finset.mem_union_right _ ?_
              rw [hFut]
              refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ ?_, hImmMem⟩
              simp only [restrictTypeOffers, Finset.mem_filter]
              exact ⟨h, hIface⟩
        have hImage : x ∈ l.alphabet.actions.image typeNeed := by
          rcases Finset.mem_union.mp hInEnv with h | h
          · exact hLocalWF.2.2.1 h
          · exact hLocalWF.2.2.2 h
        obtain ⟨y, hy, hyEq⟩ := Finset.mem_image.mp hImage
        rw [← hyEq, typeNeed_typeNeed]
        exact hy
  have hPol : l.alphabet.OnePolarity := hOneL
  obtain ⟨m, d⟩ := x
  cases d with
  | send =>
      simp only [typeNeed, MessageDir.invert] at hNeed
      rcases hComp m hIface with ⟨hSendL, _⟩ | ⟨_, hSendR⟩
      · exact absurd ⟨hSendL, hNeed⟩ (hPol m)
      · exact hSendR
  | recv =>
      simp only [typeNeed, MessageDir.invert] at hNeed
      rcases hComp m hIface with ⟨_, hRecvR⟩ | ⟨hRecvL, _⟩
      · exact hRecvR
      · exact absurd ⟨hNeed, hRecvL⟩ (hPol m)

/-- Live-equivalent residuals expose the same decorated steps.  The induction
runs on the structural half of live equivalence, because parallel children have
only *agreeing* alphabets, not equal ones; the environment's compatibility with
the other side is therefore an explicit premise. -/
theorem liveEqBody_offers_forward :
    ∀ {env : TypeEnvironment} {rho : PactType} {label : TypeLabel}
      {rho' : PactType} {current future : Finset BareMessage},
      TypeOffers env rho label rho' current future →
      ∀ {theta : PactType} {env' : TypeEnvironment},
        rho.AlphabetWellFormed → theta.AlphabetWellFormed →
        PactType.ParallelMessageOwnership rho →
        PactType.ParallelMessageOwnership theta →
        PactType.TailRecursive rho → PactType.TailRecursive theta →
        LiveEqBody rho theta →
        TypeEnvironment.AgreeOnNeeds env env'
          (PactType.MessageActions rho) →
        env'.WellFormed theta.alphabet →
        ∃ theta', TypeOffers env' theta label theta' current future ∧
          LiveEqBody rho' theta' := by
  intro env rho label rho' current future hOffers
  induction hOffers with
  | action env alphabet msg dir hEnv hMem =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, rfl, hA⟩ := liveEqBody_message_inv hLive
      have hSkip : LiveEqBody (.skip alphabet) (.skip b) := by
        simp only [LiveEqBody]
      refine ⟨.skip b, ?_, hSkip⟩
      rw [liveEqBody_preserves_futOff hSkip]
      simp only [PactType.alphabet] at hEnvT
      refine TypeOffers.action env' b msg dir
        ⟨hEnvT, (hAgree.hasNeed (by simp [PactType.MessageActions])).mp hEnv.2⟩
        ((hA _ (Finset.mem_singleton_self _)).mp hMem)
  | action_wait env alphabet msg dir hEnv hMem =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, rfl, hA⟩ := liveEqBody_message_inv hLive
      refine ⟨.message b msg dir, ?_, hLive⟩
      rw [liveEqBody_preserves_futOff hLive]
      simp only [PactType.alphabet] at hEnvT
      refine TypeOffers.action_wait env' b msg dir
        ⟨hEnvT,
          fun hNeed => hEnv.2.1
            ((hAgree.hasNeed (by simp [PactType.MessageActions])).mpr hNeed),
          by rw [← hAgree.1]; exact hEnv.2.2⟩
        ((hA _ (Finset.mem_singleton_self _)).mp hMem)
  | cycle env alphabet hEnv =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, rfl⟩ := liveEqBody_tock_inv hLive
      simp only [PactType.alphabet] at hEnvT
      exact ⟨.skip b,
        TypeOffers.cycle env' b ⟨hEnvT, by rw [← hAgree.1]; exact hEnv.2⟩,
        by simp only [LiveEqBody]⟩
  | cycle_wait env alphabet hEnv =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, rfl⟩ := liveEqBody_tock_inv hLive
      refine ⟨.tock b, ?_, hLive⟩
      rw [liveEqBody_preserves_futOff hLive]
      simp only [PactType.alphabet] at hEnvT
      exact TypeOffers.cycle_wait env' b ⟨hEnvT, by rw [← hAgree.1]; exact hEnv.2⟩
  | skip env alphabet hEnv =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, rfl⟩ := liveEqBody_skip_inv hLive
      refine ⟨.skip b, ?_, hLive⟩
      rw [liveEqBody_preserves_futOff hLive]
      simp only [PactType.alphabet] at hEnvT
      exact TypeOffers.skip env' b ⟨hEnvT, by rw [← hAgree.1]; exact hEnv.2⟩
  | progress env alphabet pid hEnv =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, rfl⟩ := liveEqBody_progress_inv hLive
      have hSkip : LiveEqBody (.skip alphabet) (.skip b) := by
        simp only [LiveEqBody]
      refine ⟨.skip b, ?_, hSkip⟩
      rw [liveEqBody_preserves_futOff hSkip]
      simp only [PactType.alphabet] at hEnvT
      exact TypeOffers.progress env' b pid ⟨hEnvT, by rw [← hAgree.1]; exact hEnv.2⟩
  | choice_left env alphabet left right hEnv =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hl, -⟩ := liveEqBody_choice_inv hLive
      refine ⟨l', ?_, hl⟩
      rw [liveEqBody_preserves_futOff hl]
      simp only [PactType.alphabet] at hEnvT
      exact TypeOffers.choice_left env' b l' r' ⟨hEnvT, by rw [← hAgree.1]; exact hEnv.2⟩
  | choice_right env alphabet left right hEnv =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, -, hr⟩ := liveEqBody_choice_inv hLive
      refine ⟨r', ?_, hr⟩
      rw [liveEqBody_preserves_futOff hr]
      simp only [PactType.alphabet] at hEnvT
      exact TypeOffers.choice_right env' b l' r' ⟨hEnvT, by rw [← hAgree.1]; exact hEnv.2⟩
  | fair_left env alphabet bid left right hEnv =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hl, -⟩ := liveEqBody_fairChoice_inv hLive
      refine ⟨l', ?_, hl⟩
      rw [liveEqBody_preserves_futOff hl]
      simp only [PactType.alphabet] at hEnvT
      exact TypeOffers.fair_left env' b bid l' r' ⟨hEnvT, by rw [← hAgree.1]; exact hEnv.2⟩
  | fair_right env alphabet bid left right hEnv =>
      intro theta env' _ _ _ _ _ _ hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, -, hr⟩ := liveEqBody_fairChoice_inv hLive
      refine ⟨r', ?_, hr⟩
      rw [liveEqBody_preserves_futOff hr]
      simp only [PactType.alphabet] at hEnvT
      exact TypeOffers.fair_right env' b bid l' r' ⟨hEnvT, by rw [← hAgree.1]; exact hEnv.2⟩
  | seq env alphabet left left' right label current childFuture hChild hNotSkip
      hNotTock ihChild =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hl, hr⟩ := liveEqBody_seq_inv hLive
      simp only [PactType.alphabet] at hEnvT
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      have hAgreeAlpha : PactTypeAlphabet.AgreeOn alphabet b
          (PactType.MessageActions (.seq alphabet left right)) := by
        simp only [LiveEqBody] at hLive; exact hLive.1
      obtain ⟨thetaLeft', hChild', hLive'⟩ :=
        ihChild hWF.2.2.2.1 hWFt.2.2.2.1
          (by rw [PactType.ParallelMessageOwnership] at hOwn; exact hOwn.1)
          (by rw [PactType.ParallelMessageOwnership] at hOwnT; exact hOwnT.1)
          (by rw [PactType.TailRecursive] at hTail; exact hTail.1)
          (by rw [PactType.TailRecursive] at hTailT; exact hTailT.1)
          hl (TypeEnvironment.AgreeOnNeeds.mono hAgree (by
            simp only [PactType.MessageActions]
            exact Finset.subset_union_left))
          (by rw [hWFt.2.1]; exact hEnvT)
      have hSkip' : thetaLeft' ≠ .skip thetaLeft'.alphabet := by
        intro hEq
        exact hNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hLive').mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      have hTargetLive : LiveEqBody (.seq alphabet left' right)
          (.seq b thetaLeft' r') := by
        simp only [LiveEqBody]
        refine ⟨?_, hLive', hr⟩
        refine hAgreeAlpha.mono ?_
        simp only [PactType.MessageActions]
        exact Finset.union_subset_union
          (typeOffers_messageActions_subset hChild) (Finset.Subset.refl _)
      refine ⟨.seq b thetaLeft' r', ?_, hTargetLive⟩
      rw [liveEqBody_preserves_futOff hTargetLive]
      exact TypeOffers.seq env' b l' thetaLeft' r' label current _ hChild'
        hSkip' hNotTock
  | seq_tock env alphabet left left' right current childFuture hChild hNotSkip
      ihChild =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hl, hr⟩ := liveEqBody_seq_inv hLive
      simp only [PactType.alphabet] at hEnvT
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      have hAgreeAlpha : PactTypeAlphabet.AgreeOn alphabet b
          (PactType.MessageActions (.seq alphabet left right)) := by
        simp only [LiveEqBody] at hLive; exact hLive.1
      obtain ⟨thetaLeft', hChild', hLive'⟩ :=
        ihChild hWF.2.2.2.1 hWFt.2.2.2.1
          (by rw [PactType.ParallelMessageOwnership] at hOwn; exact hOwn.1)
          (by rw [PactType.ParallelMessageOwnership] at hOwnT; exact hOwnT.1)
          (by rw [PactType.TailRecursive] at hTail; exact hTail.1)
          (by rw [PactType.TailRecursive] at hTailT; exact hTailT.1)
          hl (TypeEnvironment.AgreeOnNeeds.mono hAgree (by
            simp only [PactType.MessageActions]
            exact Finset.subset_union_left))
          (by rw [hWFt.2.1]; exact hEnvT)
      have hSkip' : thetaLeft' ≠ .skip thetaLeft'.alphabet := by
        intro hEq
        exact hNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hLive').mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      refine ⟨.seq b thetaLeft' r',
        TypeOffers.seq_tock env' b l' thetaLeft' r' current _ hChild' hSkip',
        ?_⟩
      simp only [LiveEqBody]
      refine ⟨?_, hLive', hr⟩
      refine hAgreeAlpha.mono ?_
      simp only [PactType.MessageActions]
      exact Finset.union_subset_union
        (typeOffers_messageActions_subset hChild) (Finset.Subset.refl _)
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ihChild =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hl, hr⟩ := liveEqBody_seq_inv hLive
      simp only [PactType.alphabet] at hEnvT
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      obtain ⟨thetaLeft', hChild', hLive'⟩ :=
        ihChild hWF.2.2.2.1 hWFt.2.2.2.1
          (by rw [PactType.ParallelMessageOwnership] at hOwn; exact hOwn.1)
          (by rw [PactType.ParallelMessageOwnership] at hOwnT; exact hOwnT.1)
          (by rw [PactType.TailRecursive] at hTail; exact hTail.1)
          (by rw [PactType.TailRecursive] at hTailT; exact hTailT.1)
          hl (TypeEnvironment.AgreeOnNeeds.mono hAgree (by
            simp only [PactType.MessageActions]
            exact Finset.subset_union_left))
          (by rw [hWFt.2.1]; exact hEnvT)
      obtain ⟨a, rfl⟩ := (liveEqBody_skip_iff hLive').mp ⟨skipAlphabet, rfl⟩
      refine ⟨r', ?_, hr⟩
      rw [liveEqBody_preserves_futOff hr]
      exact TypeOffers.seq_fuse env' b a l' r' label current _ hChild' hNotTock
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hChild ihChild =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hl, hr⟩ := liveEqBody_seq_inv hLive
      simp only [PactType.alphabet] at hEnvT
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      obtain ⟨thetaLeft', hChild', hLive'⟩ :=
        ihChild hWF.2.2.2.1 hWFt.2.2.2.1
          (by rw [PactType.ParallelMessageOwnership] at hOwn; exact hOwn.1)
          (by rw [PactType.ParallelMessageOwnership] at hOwnT; exact hOwnT.1)
          (by rw [PactType.TailRecursive] at hTail; exact hTail.1)
          (by rw [PactType.TailRecursive] at hTailT; exact hTailT.1)
          hl (TypeEnvironment.AgreeOnNeeds.mono hAgree (by
            simp only [PactType.MessageActions]
            exact Finset.subset_union_left))
          (by rw [hWFt.2.1]; exact hEnvT)
      obtain ⟨a, rfl⟩ := (liveEqBody_skip_iff hLive').mp ⟨skipAlphabet, rfl⟩
      exact ⟨r', TypeOffers.seq_fuse_tock env' b a l' r' current _ hChild', hr⟩
  | xoffer_branch env alphabet elseType branches action processType hConds
      hHeads =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, e', bs', rfl, hA, -, hbs⟩ := liveEqBody_xoffer_inv hLive
      simp only [PactType.alphabet] at hEnvT
      obtain ⟨body', hMem', hBodyLive⟩ := liveEqBranches_mem hbs hConds.2.1
      refine ⟨body', ?_, hBodyLive⟩
      rw [liveEqBody_preserves_futOff hBodyLive]
      have hHeadSub : typeBranchActions branches ⊆
          PactType.MessageActions (.xoffer alphabet elseType branches) := by
        simp only [PactType.MessageActions]
        exact Finset.Subset.trans
          (typeBranchActions_subset_branchMessageActions branches)
          Finset.subset_union_right
      refine TypeOffers.xoffer_branch env' b e' bs' action body'
        ⟨hEnvT, hMem', ?_, ?_⟩ ?_
      · exact (hAgree.2.1 action (hHeadSub (by
          simp only [typeBranchActions, List.mem_toFinset, List.mem_map]
          exact ⟨(action, processType), hConds.2.1, rfl⟩))).mp hConds.2.2.1
      · simp only [TypeResolved, ← liveEqBranches_needs hbs]
        exact typeResolved_transport hAgree hHeadSub hConds.2.2.2
      · intro x hx
        obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp
          (by rw [liveEqBranches_heads hbs]; exact List.mem_map_of_mem hx :
            x.1 ∈ branches.map Prod.fst)
        rw [← hyEq]
        refine (hA y.1 ?_).mp (hHeads y hy)
        simp only [PactType.MessageActions]
        exact Finset.mem_union_right _
          (mem_branchMessageActions_of_mem (body := y.2) (by simpa using hy))
  | xoffer_else env alphabet elseType branches hConds hHeads =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, e', bs', rfl, hA, he, hbs⟩ := liveEqBody_xoffer_inv hLive
      simp only [PactType.alphabet] at hEnvT
      refine ⟨e', ?_, he⟩
      rw [liveEqBody_preserves_futOff he]
      have hHeadSub : typeBranchActions branches ⊆
          PactType.MessageActions (.xoffer alphabet elseType branches) := by
        simp only [PactType.MessageActions]
        exact Finset.Subset.trans
          (typeBranchActions_subset_branchMessageActions branches)
          Finset.subset_union_right
      refine TypeOffers.xoffer_else env' b e' bs'
        ⟨hEnvT, by rw [← hAgree.1]; exact hConds.2.1, ?_, ?_⟩ ?_
      · simp only [TypeNoImmediateBranch, ← liveEqBranches_needs hbs]
        exact typeNoImmediateBranch_transport hAgree hHeadSub hConds.2.2.1
      · simp only [TypeResolved, ← liveEqBranches_needs hbs]
        exact typeResolved_transport hAgree hHeadSub hConds.2.2.2
      · intro x hx
        obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp
          (by rw [liveEqBranches_heads hbs]; exact List.mem_map_of_mem hx :
            x.1 ∈ branches.map Prod.fst)
        rw [← hyEq]
        refine (hA y.1 ?_).mp (hHeads y hy)
        simp only [PactType.MessageActions]
        exact Finset.mem_union_right _
          (mem_branchMessageActions_of_mem (body := y.2) (by simpa using hy))
  | xoffer_wait env alphabet elseType branches hConds hHeads =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, e', bs', rfl, hA, he, hbs⟩ := liveEqBody_xoffer_inv hLive
      simp only [PactType.alphabet] at hEnvT
      have hHeadSubEarly : typeBranchActions branches ⊆
          PactType.MessageActions (.xoffer alphabet elseType branches) := by
        simp only [PactType.MessageActions]
        exact Finset.Subset.trans
          (typeBranchActions_subset_branchMessageActions branches)
          Finset.subset_union_right
      refine ⟨.xoffer b e' bs', ?_, hLive⟩
      rw [liveEqBody_preserves_futOff hLive,
        show typeWaitingOffers env branches = typeWaitingOffers env' bs' from by
          rw [typeWaitingOffers_transport hAgree hHeadSubEarly]
          simp only [typeWaitingOffers, liveEqBranches_actions hbs]]
      have hHeadSub : typeBranchActions branches ⊆
          PactType.MessageActions (.xoffer alphabet elseType branches) := by
        simp only [PactType.MessageActions]
        exact Finset.Subset.trans
          (typeBranchActions_subset_branchMessageActions branches)
          Finset.subset_union_right
      refine TypeOffers.xoffer_wait env' b e' bs'
        ⟨hEnvT, ?_, by rw [← hAgree.1]; exact hConds.2.2⟩ ?_
      · simp only [TypeResolved, ← liveEqBranches_needs hbs]
        exact typeResolved_not_transport hAgree hHeadSub hConds.2.1
      · intro x hx
        obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp
          (by rw [liveEqBranches_heads hbs]; exact List.mem_map_of_mem hx :
            x.1 ∈ branches.map Prod.fst)
        rw [← hyEq]
        refine (hA y.1 ?_).mp (hHeads y hy)
        simp only [PactType.MessageActions]
        exact Finset.mem_union_right _
          (mem_branchMessageActions_of_mem (body := y.2) (by simpa using hy))
  | offer_else env alphabet elseType branches hConds hHeads =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, e', bs', rfl, hA, he, hbs⟩ := liveEqBody_offer_inv hLive
      simp only [PactType.alphabet] at hEnvT
      refine ⟨e', ?_, he⟩
      rw [liveEqBody_preserves_futOff he, liveEqBranches_actions hbs]
      have hHeadSub : typeBranchActions branches ⊆
          PactType.MessageActions (.offer alphabet elseType branches) := by
        simp only [PactType.MessageActions]
        exact Finset.Subset.trans
          (typeBranchActions_subset_branchMessageActions branches)
          Finset.subset_union_right
      refine TypeOffers.offer_else env' b e' bs'
        ⟨hEnvT, by rw [← hAgree.1]; exact hConds.2.1, ?_, ?_⟩ ?_
      · simp only [TypeNoImmediateBranch, ← liveEqBranches_needs hbs]
        exact typeNoImmediateBranch_transport hAgree hHeadSub hConds.2.2.1
      · simp only [TypeResolved, ← liveEqBranches_needs hbs]
        exact typeResolved_transport hAgree hHeadSub hConds.2.2.2
      · intro x hx
        obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp
          (by rw [liveEqBranches_heads hbs]; exact List.mem_map_of_mem hx :
            x.1 ∈ branches.map Prod.fst)
        rw [← hyEq]
        refine (hA y.1 ?_).mp (hHeads y hy)
        simp only [PactType.MessageActions]
        exact Finset.mem_union_right _
          (mem_branchMessageActions_of_mem (body := y.2) (by simpa using hy))
  | offer_wait env alphabet elseType branches hConds hHeads =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, e', bs', rfl, hA, he, hbs⟩ := liveEqBody_offer_inv hLive
      simp only [PactType.alphabet] at hEnvT
      refine ⟨.offer b e' bs', ?_, hLive⟩
      rw [liveEqBody_preserves_futOff hLive, liveEqBranches_actions hbs]
      have hHeadSub : typeBranchActions branches ⊆
          PactType.MessageActions (.offer alphabet elseType branches) := by
        simp only [PactType.MessageActions]
        exact Finset.Subset.trans
          (typeBranchActions_subset_branchMessageActions branches)
          Finset.subset_union_right
      refine TypeOffers.offer_wait env' b e' bs'
        ⟨hEnvT, by rw [← hAgree.1]; exact hConds.2.1, ?_, ?_⟩ ?_
      · simp only [TypeNoImmediateBranch, ← liveEqBranches_needs hbs]
        exact typeNoImmediateBranch_transport hAgree hHeadSub hConds.2.2.1
      · simp only [TypeResolved, ← liveEqBranches_needs hbs]
        exact typeResolved_not_transport hAgree hHeadSub hConds.2.2.2
      · intro x hx
        obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp
          (by rw [liveEqBranches_heads hbs]; exact List.mem_map_of_mem hx :
            x.1 ∈ branches.map Prod.fst)
        rw [← hyEq]
        refine (hA y.1 ?_).mp (hHeads y hy)
        simp only [PactType.MessageActions]
        exact Finset.mem_union_right _
          (mem_branchMessageActions_of_mem (body := y.2) (by simpa using hy))
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hAliveL
      hAliveR hStepL hStepR hNotBoth hLocalL hLocalR hWFSync ihL ihR =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hA, hl, hr⟩ := liveEqBody_par_inv hLive
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      simp only [PactType.ParallelMessageOwnership] at hOwn hOwnT
      simp only [PactType.TailRecursive] at hTail hTailT
      obtain rfl := PactTypeAlphabet.parent_eq_mergeHidden hWFt.2.1 hOwnT.2.1
      simp only [PactType.alphabet] at hEnvT
      have hAgreeL := liveEqBody_agreeOn hl
      have hAgreeR := liveEqBody_agreeOn hr
      obtain ⟨leftEnv', rightEnv', hLocalL', hLocalR', hEnvL, hEnvR⟩ :=
        parLocalEnvs_transport hLocalL hLocalR
          (by simpa only [PactType.MessageActions] using hAgree) hAgreeL hAgreeR
      have hOfferL : ∀ x ∈ leftCurrent ∪ leftFuture,
          x ∈ PactType.MessageActions left := by
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · exact typeOffers_current_subset hStepL h
        · exact typeOffers_future_subset_messageActions hStepL h
      have hOfferR : ∀ x ∈ rightCurrent ∪ rightFuture,
          x ∈ PactType.MessageActions right := by
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · exact typeOffers_current_subset hStepR h
        · exact typeOffers_future_subset_messageActions hStepR h
      have hCompSwap : PactTypeAlphabet.ComplementaryOn right.alphabet
          left.alphabet interface := fun m hm =>
        (hWF.2.1.complementary m hm).elim (fun h => Or.inr ⟨h.2, h.1⟩)
          (fun h => Or.inl ⟨h.2, h.1⟩)
      have hCompSwapT : PactTypeAlphabet.ComplementaryOn r'.alphabet
          l'.alphabet interface := fun m hm =>
        (hWFt.2.1.complementary m hm).elim (fun h => Or.inr ⟨h.2, h.1⟩)
          (fun h => Or.inl ⟨h.2, h.1⟩)
      have hDeclR : outer.clock = false → ∀ x ∈ rightCurrent ∪ rightFuture,
          x.1 ∈ interface → x ∈ r'.alphabet.actions := fun hClock x hx hIface =>
        (hAgreeR x (hOfferR x hx)).mp
          (sibling_offer_declared hLocalL
            (typeOffers_env_wellFormed hStepL hWF.2.2.1)
            hWF.2.1.complementary hWF.2.2.1.alphabet_wellFormed hClock hx
            hIface)
      have hDeclL : outer.clock = false → ∀ x ∈ leftCurrent ∪ leftFuture,
          x.1 ∈ interface → x ∈ l'.alphabet.actions := fun hClock x hx hIface =>
        (hAgreeL x (hOfferL x hx)).mp
          (sibling_offer_declared hLocalR
            (typeOffers_env_wellFormed hStepR hWF.2.2.2) hCompSwap
            hWF.2.2.2.alphabet_wellFormed hClock hx hIface)
      have hWFL : leftEnv'.WellFormed l'.alphabet :=
        localEnv_wellFormed_interface hLocalL' hWFt.2.1.complementary
          hWFt.2.2.1.alphabet_wellFormed hWFt.2.2.2.alphabet_wellFormed
          (fun hClock x hx => hDeclR (hAgree.1.trans hClock) x
            (Finset.mem_union_left _ hx))
          (fun hClock x hx => hDeclR (hAgree.1.trans hClock) x
            (Finset.mem_union_right _ hx))
      have hWFR : rightEnv'.WellFormed r'.alphabet :=
        localEnv_wellFormed_interface hLocalR' hCompSwapT
          hWFt.2.2.2.alphabet_wellFormed hWFt.2.2.1.alphabet_wellFormed
          (fun hClock x hx => hDeclL (hAgree.1.trans hClock) x
            (Finset.mem_union_left _ hx))
          (fun hClock x hx => hDeclL (hAgree.1.trans hClock) x
            (Finset.mem_union_right _ hx))
      obtain ⟨lTarget', hStepL', hLiveL'⟩ :=
        ihL hWF.2.2.1 hWFt.2.2.1 hOwn.2.2.1 hOwnT.2.2.1 hTail.1 hTailT.1 hl
          hEnvL hWFL
      obtain ⟨rTarget', hStepR', hLiveR'⟩ :=
        ihR hWF.2.2.2 hWFt.2.2.2 hOwn.2.2.2 hOwnT.2.2.2 hTail.2 hTailT.2 hr
          hEnvR hWFR
      have hAliveL' : l' ≠ PactType.skip l'.alphabet := by
        intro hEq
        exact hAliveL (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hl).mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      have hAliveR' : r' ≠ PactType.skip r'.alphabet := by
        intro hEq
        exact hAliveR (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hr).mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      have hNotBoth' : ¬ (lTarget' = PactType.skip lTarget'.alphabet ∧
          rTarget' = PactType.skip rTarget'.alphabet) := by
        rintro ⟨hL, hR⟩
        refine hNotBoth ⟨?_, ?_⟩
        · obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hLiveL').mpr ⟨_, hL⟩
          rw [ha]; simp [PactType.alphabet]
        · obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hLiveR').mpr ⟨_, hR⟩
          rw [ha]; simp [PactType.alphabet]
      have hTargetLive : LiveEqBody
          (.par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet
            interface) left' right' interface)
          (.par (PactTypeAlphabet.mergeHidden l'.alphabet r'.alphabet
            interface) lTarget' rTarget' interface) := by
        simp only [LiveEqBody]
        refine ⟨trivial, ?_, hLiveL', hLiveR'⟩
        refine hA.mono ?_
        simp only [PactType.MessageActions]
        exact Finset.union_subset_union
          (typeOffers_messageActions_subset hStepL)
          (typeOffers_messageActions_subset hStepR)
      refine ⟨.par (PactTypeAlphabet.mergeHidden l'.alphabet r'.alphabet
        interface) lTarget' rTarget' interface, ?_, hTargetLive⟩
      rw [liveEqBody_preserves_futOff hTargetLive]
      exact TypeOffers.par env' leftEnv' rightEnv' interface l' lTarget' r'
        rTarget' leftLabel rightLabel leftCurrent leftFuture rightCurrent
        rightFuture hAliveL' hAliveR' hStepL' hStepR' hNotBoth' hLocalL'
        hLocalR' ⟨hEnvT, hWFSync.2⟩
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hStepL hStepR hLocalL
      hLocalR hWFSync hNotTock ihL ihR =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hA, hl, hr⟩ := liveEqBody_par_inv hLive
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      simp only [PactType.ParallelMessageOwnership] at hOwn hOwnT
      simp only [PactType.TailRecursive] at hTail hTailT
      obtain rfl := PactTypeAlphabet.parent_eq_mergeHidden hWFt.2.1 hOwnT.2.1
      simp only [PactType.alphabet] at hEnvT
      have hAgreeL := liveEqBody_agreeOn hl
      have hAgreeR := liveEqBody_agreeOn hr
      obtain ⟨leftEnv', rightEnv', hLocalL', hLocalR', hEnvL, hEnvR⟩ :=
        parLocalEnvs_transport hLocalL hLocalR
          (by simpa only [PactType.MessageActions] using hAgree) hAgreeL hAgreeR
      have hFutL : leftFuture = ∅ :=
        TypeOffers.future_eq_empty_of_target_skip hStepL rfl
      have hFutR : rightFuture = ∅ :=
        TypeOffers.future_eq_empty_of_target_skip hStepR rfl
      have hCurL : leftCurrent ⊆ l'.alphabet.actions := fun x hx =>
        (hAgreeL x (typeOffers_current_subset hStepL hx)).mp
          (typeOffers_current_subset_alphabet hWF.2.2.1 hStepL hx)
      have hCurR : rightCurrent ⊆ r'.alphabet.actions := fun x hx =>
        (hAgreeR x (typeOffers_current_subset hStepR hx)).mp
          (typeOffers_current_subset_alphabet hWF.2.2.2 hStepR hx)
      have hComp := hWFt.2.1.complementary
      have hWFL : leftEnv'.WellFormed l'.alphabet :=
        localEnv_wellFormed hLocalL' hComp hWFt.2.2.1.alphabet_wellFormed
          hWFt.2.2.2.alphabet_wellFormed hCurR
          (by rw [hFutR]; exact Finset.empty_subset _)
      have hWFR : rightEnv'.WellFormed r'.alphabet :=
        localEnv_wellFormed hLocalR'
          (fun m hm => (hComp m hm).elim (fun h => Or.inr ⟨h.2, h.1⟩)
            (fun h => Or.inl ⟨h.2, h.1⟩))
          hWFt.2.2.2.alphabet_wellFormed hWFt.2.2.1.alphabet_wellFormed hCurL
          (by rw [hFutL]; exact Finset.empty_subset _)
      obtain ⟨lTarget', hStepL', hLiveL'⟩ :=
        ihL hWF.2.2.1 hWFt.2.2.1 hOwn.2.2.1 hOwnT.2.2.1 hTail.1 hTailT.1 hl
          hEnvL hWFL
      obtain ⟨rTarget', hStepR', hLiveR'⟩ :=
        ihR hWF.2.2.2 hWFt.2.2.2 hOwn.2.2.2 hOwnT.2.2.2 hTail.2 hTailT.2 hr
          hEnvR hWFR
      obtain ⟨aL, rfl⟩ := liveEqBody_skip_inv hLiveL'
      obtain ⟨aR, rfl⟩ := liveEqBody_skip_inv hLiveR'
      obtain rfl : aL = l'.alphabet := by
        simpa only [PactType.alphabet] using
          TypeOffers.preserves_alphabet hWFt.2.2.1 hStepL'
      obtain rfl : aR = r'.alphabet := by
        simpa only [PactType.alphabet] using
          TypeOffers.preserves_alphabet hWFt.2.2.2 hStepR'
      refine ⟨.skip (PactTypeAlphabet.mergeHidden l'.alphabet r'.alphabet
          interface),
        TypeOffers.par_fuse env' leftEnv' rightEnv' interface l' r' leftLabel
          rightLabel leftCurrent leftFuture rightCurrent rightFuture hStepL'
          hStepR' hLocalL' hLocalR' ⟨hEnvT, hWFSync.2⟩ hNotTock, ?_⟩
      simp only [LiveEqBody]
  | par_fuse_tock outer leftEnv rightEnv interface left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hStepL hStepR
      hLocalL hLocalR hWFSync hTock ihL ihR =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hA, hl, hr⟩ := liveEqBody_par_inv hLive
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      simp only [PactType.ParallelMessageOwnership] at hOwn hOwnT
      simp only [PactType.TailRecursive] at hTail hTailT
      obtain rfl := PactTypeAlphabet.parent_eq_mergeHidden hWFt.2.1 hOwnT.2.1
      simp only [PactType.alphabet] at hEnvT
      have hAgreeL := liveEqBody_agreeOn hl
      have hAgreeR := liveEqBody_agreeOn hr
      obtain ⟨leftEnv', rightEnv', hLocalL', hLocalR', hEnvL, hEnvR⟩ :=
        parLocalEnvs_transport hLocalL hLocalR
          (by simpa only [PactType.MessageActions] using hAgree) hAgreeL hAgreeR
      have hFutL : leftFuture = ∅ :=
        TypeOffers.future_eq_empty_of_target_skip hStepL rfl
      have hFutR : rightFuture = ∅ :=
        TypeOffers.future_eq_empty_of_target_skip hStepR rfl
      have hCurL : leftCurrent ⊆ l'.alphabet.actions := fun x hx =>
        (hAgreeL x (typeOffers_current_subset hStepL hx)).mp
          (typeOffers_current_subset_alphabet hWF.2.2.1 hStepL hx)
      have hCurR : rightCurrent ⊆ r'.alphabet.actions := fun x hx =>
        (hAgreeR x (typeOffers_current_subset hStepR hx)).mp
          (typeOffers_current_subset_alphabet hWF.2.2.2 hStepR hx)
      have hComp := hWFt.2.1.complementary
      have hWFL : leftEnv'.WellFormed l'.alphabet :=
        localEnv_wellFormed hLocalL' hComp hWFt.2.2.1.alphabet_wellFormed
          hWFt.2.2.2.alphabet_wellFormed hCurR
          (by rw [hFutR]; exact Finset.empty_subset _)
      have hWFR : rightEnv'.WellFormed r'.alphabet :=
        localEnv_wellFormed hLocalR'
          (fun m hm => (hComp m hm).elim (fun h => Or.inr ⟨h.2, h.1⟩)
            (fun h => Or.inl ⟨h.2, h.1⟩))
          hWFt.2.2.2.alphabet_wellFormed hWFt.2.2.1.alphabet_wellFormed hCurL
          (by rw [hFutL]; exact Finset.empty_subset _)
      obtain ⟨lTarget', hStepL', hLiveL'⟩ :=
        ihL hWF.2.2.1 hWFt.2.2.1 hOwn.2.2.1 hOwnT.2.2.1 hTail.1 hTailT.1 hl
          hEnvL hWFL
      obtain ⟨rTarget', hStepR', hLiveR'⟩ :=
        ihR hWF.2.2.2 hWFt.2.2.2 hOwn.2.2.2 hOwnT.2.2.2 hTail.2 hTailT.2 hr
          hEnvR hWFR
      obtain ⟨aL, rfl⟩ := liveEqBody_skip_inv hLiveL'
      obtain ⟨aR, rfl⟩ := liveEqBody_skip_inv hLiveR'
      obtain rfl : aL = l'.alphabet := by
        simpa only [PactType.alphabet] using
          TypeOffers.preserves_alphabet hWFt.2.2.1 hStepL'
      obtain rfl : aR = r'.alphabet := by
        simpa only [PactType.alphabet] using
          TypeOffers.preserves_alphabet hWFt.2.2.2 hStepR'
      refine ⟨.skip (PactTypeAlphabet.mergeHidden l'.alphabet r'.alphabet
          interface),
        TypeOffers.par_fuse_tock env' leftEnv' rightEnv' interface l' r'
          leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
          hStepL' hStepR' hLocalL' hLocalR' ⟨hEnvT, hWFSync.2⟩ hTock, ?_⟩
      simp only [LiveEqBody]
  | left_complete outer rightEnv interface left right right' rightLabel
      rightCurrent rightFuture hLeftSkip hRightNotSkip hStep hTargetNotSkip
      hRestrictC hRestrictF hLocal hOuterWF hNotTock ih =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hA, hl, hr⟩ := liveEqBody_par_inv hLive
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      simp only [PactType.ParallelMessageOwnership] at hOwn hOwnT
      simp only [PactType.TailRecursive] at hTail hTailT
      obtain rfl := PactTypeAlphabet.parent_eq_mergeHidden hWFt.2.1 hOwnT.2.1
      simp only [PactType.alphabet] at hEnvT
      have hAgreeR := liveEqBody_agreeOn hr
      obtain ⟨rightEnv', hLocal', hEnvR⟩ :=
        localEnv_transport_solo hLocal
          (hAgree.mono (by
            simp only [PactType.MessageActions]
            exact Finset.subset_union_right)) hAgreeR
      have hComp := hWFt.2.1.complementary
      have hWFR : rightEnv'.WellFormed r'.alphabet :=
        localEnv_wellFormed hLocal'
          (fun m hm => (hComp m hm).elim (fun h => Or.inr ⟨h.2, h.1⟩)
            (fun h => Or.inl ⟨h.2, h.1⟩))
          hWFt.2.2.2.alphabet_wellFormed hWFt.2.2.1.alphabet_wellFormed
          (Finset.empty_subset _) (Finset.empty_subset _)
      obtain ⟨rTarget', hStep', hLive'⟩ :=
        ih hWF.2.2.2 hWFt.2.2.2 hOwn.2.2.2 hOwnT.2.2.2 hTail.2 hTailT.2 hr
          hEnvR hWFR
      have hSkipL' : l' = PactType.skip l'.alphabet := by
        obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hl).mp ⟨left.alphabet, hLeftSkip⟩
        rw [ha]; simp [PactType.alphabet]
      have hNotSkipR' : r' ≠ PactType.skip r'.alphabet := by
        intro hEq
        exact hRightNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hr).mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      have hNotSkipT' : rTarget' ≠ PactType.skip rTarget'.alphabet := by
        intro hEq
        exact hTargetNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hLive').mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      have hReann : LiveEqBody
          (right'.reannotate (PactTypeAlphabet.mergeHidden left.alphabet
            right.alphabet interface))
          (rTarget'.reannotate (PactTypeAlphabet.mergeHidden l'.alphabet
            r'.alphabet interface)) :=
        liveEqBody_reannotate
          (hA.mono (by
            simp only [PactType.MessageActions]
            exact Finset.Subset.trans (typeOffers_messageActions_subset hStep)
              Finset.subset_union_right)) hLive'
      refine ⟨rTarget'.reannotate (PactTypeAlphabet.mergeHidden l'.alphabet
        r'.alphabet interface), ?_, hReann⟩
      rw [liveEqBody_preserves_futOff hReann]
      exact TypeOffers.left_complete env' rightEnv' interface l' r' rTarget'
        rightLabel rightCurrent rightFuture hSkipL' hNotSkipR' hStep'
        hNotSkipT' hRestrictC hRestrictF hLocal' hEnvT hNotTock
  | left_complete_tock outer rightEnv interface left right right' rightLabel
      rightCurrent rightFuture hLeftSkip hRightNotSkip hStep hTargetNotSkip
      hRestrictC hRestrictF hLocal hOuterWF hTock ih =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hA, hl, hr⟩ := liveEqBody_par_inv hLive
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      simp only [PactType.ParallelMessageOwnership] at hOwn hOwnT
      simp only [PactType.TailRecursive] at hTail hTailT
      obtain rfl := PactTypeAlphabet.parent_eq_mergeHidden hWFt.2.1 hOwnT.2.1
      simp only [PactType.alphabet] at hEnvT
      have hAgreeR := liveEqBody_agreeOn hr
      obtain ⟨rightEnv', hLocal', hEnvR⟩ :=
        localEnv_transport_solo hLocal
          (hAgree.mono (by
            simp only [PactType.MessageActions]
            exact Finset.subset_union_right)) hAgreeR
      have hComp := hWFt.2.1.complementary
      have hWFR : rightEnv'.WellFormed r'.alphabet :=
        localEnv_wellFormed hLocal'
          (fun m hm => (hComp m hm).elim (fun h => Or.inr ⟨h.2, h.1⟩)
            (fun h => Or.inl ⟨h.2, h.1⟩))
          hWFt.2.2.2.alphabet_wellFormed hWFt.2.2.1.alphabet_wellFormed
          (Finset.empty_subset _) (Finset.empty_subset _)
      obtain ⟨rTarget', hStep', hLive'⟩ :=
        ih hWF.2.2.2 hWFt.2.2.2 hOwn.2.2.2 hOwnT.2.2.2 hTail.2 hTailT.2 hr
          hEnvR hWFR
      have hSkipL' : l' = PactType.skip l'.alphabet := by
        obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hl).mp ⟨left.alphabet, hLeftSkip⟩
        rw [ha]; simp [PactType.alphabet]
      have hNotSkipR' : r' ≠ PactType.skip r'.alphabet := by
        intro hEq
        exact hRightNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hr).mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      have hNotSkipT' : rTarget' ≠ PactType.skip rTarget'.alphabet := by
        intro hEq
        exact hTargetNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hLive').mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      exact ⟨rTarget'.reannotate (PactTypeAlphabet.mergeHidden l'.alphabet
          r'.alphabet interface),
        TypeOffers.left_complete_tock env' rightEnv' interface l' r' rTarget'
          rightLabel rightCurrent rightFuture hSkipL' hNotSkipR' hStep'
          hNotSkipT' hRestrictC hRestrictF hLocal' hEnvT hTock,
        liveEqBody_reannotate
          (hA.mono (by
            simp only [PactType.MessageActions]
            exact Finset.Subset.trans (typeOffers_messageActions_subset hStep)
              Finset.subset_union_right)) hLive'⟩
  | right_complete outer leftEnv interface left left' right leftLabel
      leftCurrent leftFuture hRightSkip hLeftNotSkip hStep hTargetNotSkip
      hRestrictC hRestrictF hLocal hOuterWF hNotTock ih =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hA, hl, hr⟩ := liveEqBody_par_inv hLive
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      simp only [PactType.ParallelMessageOwnership] at hOwn hOwnT
      simp only [PactType.TailRecursive] at hTail hTailT
      obtain rfl := PactTypeAlphabet.parent_eq_mergeHidden hWFt.2.1 hOwnT.2.1
      simp only [PactType.alphabet] at hEnvT
      have hAgreeL := liveEqBody_agreeOn hl
      obtain ⟨leftEnv', hLocal', hEnvL⟩ :=
        localEnv_transport_solo hLocal
          (hAgree.mono (by
            simp only [PactType.MessageActions]
            exact Finset.subset_union_left)) hAgreeL
      have hWFL : leftEnv'.WellFormed l'.alphabet :=
        localEnv_wellFormed hLocal' hWFt.2.1.complementary
          hWFt.2.2.1.alphabet_wellFormed hWFt.2.2.2.alphabet_wellFormed
          (Finset.empty_subset _) (Finset.empty_subset _)
      obtain ⟨lTarget', hStep', hLive'⟩ :=
        ih hWF.2.2.1 hWFt.2.2.1 hOwn.2.2.1 hOwnT.2.2.1 hTail.1 hTailT.1 hl
          hEnvL hWFL
      have hSkipR' : r' = PactType.skip r'.alphabet := by
        obtain ⟨a, ha⟩ :=
          (liveEqBody_skip_iff hr).mp ⟨right.alphabet, hRightSkip⟩
        rw [ha]; simp [PactType.alphabet]
      have hNotSkipL' : l' ≠ PactType.skip l'.alphabet := by
        intro hEq
        exact hLeftNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hl).mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      have hNotSkipT' : lTarget' ≠ PactType.skip lTarget'.alphabet := by
        intro hEq
        exact hTargetNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hLive').mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      have hReann : LiveEqBody
          (left'.reannotate (PactTypeAlphabet.mergeHidden left.alphabet
            right.alphabet interface))
          (lTarget'.reannotate (PactTypeAlphabet.mergeHidden l'.alphabet
            r'.alphabet interface)) :=
        liveEqBody_reannotate
          (hA.mono (by
            simp only [PactType.MessageActions]
            exact Finset.Subset.trans (typeOffers_messageActions_subset hStep)
              Finset.subset_union_left)) hLive'
      refine ⟨lTarget'.reannotate (PactTypeAlphabet.mergeHidden l'.alphabet
        r'.alphabet interface), ?_, hReann⟩
      rw [liveEqBody_preserves_futOff hReann]
      exact TypeOffers.right_complete env' leftEnv' interface l' lTarget' r'
        leftLabel leftCurrent leftFuture hSkipR' hNotSkipL' hStep' hNotSkipT'
        hRestrictC hRestrictF hLocal' hEnvT hNotTock
  | right_complete_tock outer leftEnv interface left left' right leftLabel
      leftCurrent leftFuture hRightSkip hLeftNotSkip hStep hTargetNotSkip
      hRestrictC hRestrictF hLocal hOuterWF hTock ih =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, l', r', rfl, hA, hl, hr⟩ := liveEqBody_par_inv hLive
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      simp only [PactType.ParallelMessageOwnership] at hOwn hOwnT
      simp only [PactType.TailRecursive] at hTail hTailT
      obtain rfl := PactTypeAlphabet.parent_eq_mergeHidden hWFt.2.1 hOwnT.2.1
      simp only [PactType.alphabet] at hEnvT
      have hAgreeL := liveEqBody_agreeOn hl
      obtain ⟨leftEnv', hLocal', hEnvL⟩ :=
        localEnv_transport_solo hLocal
          (hAgree.mono (by
            simp only [PactType.MessageActions]
            exact Finset.subset_union_left)) hAgreeL
      have hWFL : leftEnv'.WellFormed l'.alphabet :=
        localEnv_wellFormed hLocal' hWFt.2.1.complementary
          hWFt.2.2.1.alphabet_wellFormed hWFt.2.2.2.alphabet_wellFormed
          (Finset.empty_subset _) (Finset.empty_subset _)
      obtain ⟨lTarget', hStep', hLive'⟩ :=
        ih hWF.2.2.1 hWFt.2.2.1 hOwn.2.2.1 hOwnT.2.2.1 hTail.1 hTailT.1 hl
          hEnvL hWFL
      have hSkipR' : r' = PactType.skip r'.alphabet := by
        obtain ⟨a, ha⟩ :=
          (liveEqBody_skip_iff hr).mp ⟨right.alphabet, hRightSkip⟩
        rw [ha]; simp [PactType.alphabet]
      have hNotSkipL' : l' ≠ PactType.skip l'.alphabet := by
        intro hEq
        exact hLeftNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hl).mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      have hNotSkipT' : lTarget' ≠ PactType.skip lTarget'.alphabet := by
        intro hEq
        exact hTargetNotSkip (by
          obtain ⟨a, ha⟩ := (liveEqBody_skip_iff hLive').mpr ⟨_, hEq⟩
          rw [ha]; simp [PactType.alphabet])
      exact ⟨lTarget'.reannotate (PactTypeAlphabet.mergeHidden l'.alphabet
          r'.alphabet interface),
        TypeOffers.right_complete_tock env' leftEnv' interface l' lTarget' r'
          leftLabel leftCurrent leftFuture hSkipR' hNotSkipL' hStep' hNotSkipT'
          hRestrictC hRestrictF hLocal' hEnvT hTock,
        liveEqBody_reannotate
          (hA.mono (by
            simp only [PactType.MessageActions]
            exact Finset.Subset.trans (typeOffers_messageActions_subset hStep)
              Finset.subset_union_left)) hLive'⟩
  | recur env alphabet name body hEnv =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, body', rfl, hA, hBody⟩ := liveEqBody_recur_inv hLive
      simp only [PactType.alphabet] at hEnvT
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      simp only [PactType.TailRecursive] at hTail
      have hAgreeBody : PactTypeAlphabet.AgreeOn body.alphabet body'.alphabet
          (PactType.MessageActions (PactType.recur alphabet name body)) := by
        rw [hWF.2.1, hWFt.2.1]
        simpa only [PactType.MessageActions] using hA
      have hTargetLive : LiveEqBody
          (body.replaceVar name (PactType.recur alphabet name body))
          (body'.replaceVar name (PactType.recur b name body')) :=
        (liveEqBody_replaceVar_fuel name hLive hAgreeBody (sizeOf body) body
          body' le_rfl hBody hWF.2.2 hWFt.2.2 rfl rfl hTail.1).1
      refine ⟨body'.replaceVar name (PactType.recur b name body'), ?_,
        hTargetLive⟩
      rw [liveEqBody_preserves_futOff hTargetLive]
      exact TypeOffers.recur env' b name body'
        ⟨hEnvT, by rw [← hAgree.1]; exact hEnv.2⟩
  | offer_some env alphabet elseType branches enabled hConds hHeads =>
      intro theta env' hWF hWFt hOwn hOwnT hTail hTailT hLive hAgree hEnvT
      obtain ⟨b, e', bs', rfl, hA, he, hbs⟩ := liveEqBody_offer_inv hLive
      simp only [PactType.alphabet] at hEnvT
      simp only [PactType.AlphabetWellFormed] at hWF hWFt
      simp only [PactType.ParallelMessageOwnership] at hOwn hOwnT
      obtain ⟨eAction, eBody⟩ := enabled
      obtain ⟨body', hMem', hBodyLive⟩ := liveEqBranches_mem hbs hConds.2.1
      have hHeadSub : typeBranchActions branches ⊆
          PactType.MessageActions (.offer alphabet elseType branches) := by
        simp only [PactType.MessageActions]
        exact Finset.Subset.trans
          (typeBranchActions_subset_branchMessageActions branches)
          Finset.subset_union_right
      have hProd : LiveEqBody
          (parallelTypeBranchesSelecting alphabet (eAction, eBody) branches)
          (parallelTypeBranchesSelecting b (eAction, body') bs') :=
        liveEqBody_parallelTypeBranchesSelecting_of_ownership hbs
          (hA.mono (by
            simp only [PactType.MessageActions]
            exact Finset.subset_union_right))
          hWF.2.2.2 hWFt.2.2.2 hOwn.2 hOwnT.2 hConds.2.1 hMem' rfl
      refine ⟨parallelTypeBranchesSelecting b (eAction, body') bs', ?_, hProd⟩
      rw [liveEqBody_preserves_futOff hProd]
      refine TypeOffers.offer_some env' b e' bs' (eAction, body')
        ⟨hEnvT, hMem', ?_⟩ ?_
      · exact (hAgree.2.1 eAction (hHeadSub (by
          simp only [typeBranchActions, List.mem_toFinset, List.mem_map]
          exact ⟨(eAction, eBody), hConds.2.1, rfl⟩))).mp hConds.2.2
      · intro x hx
        obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp
          (by rw [liveEqBranches_heads hbs]; exact List.mem_map_of_mem hx :
            x.1 ∈ branches.map Prod.fst)
        rw [← hyEq]
        refine (hA y.1 ?_).mp (hHeads y hy)
        simp only [PactType.MessageActions]
        exact Finset.mem_union_right _
          (mem_branchMessageActions_of_mem (body := y.2) (by simpa using hy))


/-- The paper's statement: live-equivalent residuals match each other's
decorated steps.  Equal outer alphabets make the environment premise trivial. -/
theorem liveEq_step_forward {env : TypeEnvironment} {rho theta rho' : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hWF : rho.AlphabetWellFormed) (hWFt : theta.AlphabetWellFormed)
    (hOwn : PactType.ParallelMessageOwnership rho)
    (hOwnT : PactType.ParallelMessageOwnership theta)
    (hTail : rho.TailRecursive) (hTailT : theta.TailRecursive)
    (hLive : LiveEq rho theta)
    (hStep : TypeOffers env rho label rho' current future) :
    ∃ theta', TypeOffers env theta label theta' current future ∧
      LiveEqBody rho' theta' :=
  liveEqBody_offers_forward hStep hWF hWFt hOwn hOwnT hTail hTailT hLive.2
    (TypeEnvironment.AgreeOnNeeds.refl _ _)
    (by rw [← hLive.1]; exact typeOffers_env_wellFormed hStep hWF)

/-- The same implication with the two residuals exchanged. -/
theorem liveEq_step_backward {env : TypeEnvironment} {rho theta theta' : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hWF : rho.AlphabetWellFormed) (hWFt : theta.AlphabetWellFormed)
    (hOwn : PactType.ParallelMessageOwnership rho)
    (hOwnT : PactType.ParallelMessageOwnership theta)
    (hTail : rho.TailRecursive) (hTailT : theta.TailRecursive)
    (hLive : LiveEq rho theta)
    (hStep : TypeOffers env theta label theta' current future) :
    ∃ rho', TypeOffers env rho label rho' current future ∧
      LiveEqBody theta' rho' :=
  liveEq_step_forward hWFt hWF hOwnT hOwn hTailT hTail (liveEq_symm hLive) hStep

/-- The decorated form of the transfer: the underlying transition moves with the
offers. -/
theorem liveEq_decorated_forward {env : TypeEnvironment} {rho theta rho' : PactType}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hWF : rho.AlphabetWellFormed) (hWFt : theta.AlphabetWellFormed)
    (hOwn : PactType.ParallelMessageOwnership rho)
    (hOwnT : PactType.ParallelMessageOwnership theta)
    (hTail : rho.TailRecursive) (hTailT : theta.TailRecursive)
    (hLive : LiveEq rho theta)
    (hStep : DecoratedTypeTransition env rho label offers rho') :
    ∃ theta', DecoratedTypeTransition env theta label offers theta' ∧
      LiveEqBody rho' theta' := by
  obtain ⟨theta', hOffers, hLive'⟩ :=
    liveEq_step_forward hWF hWFt hOwn hOwnT hTail hTailT hLive hStep.2
  exact ⟨theta', hOffers.toDecorated, hLive'⟩

/-- The same implication with the two residuals exchanged. -/
theorem liveEq_decorated_backward {env : TypeEnvironment} {rho theta theta' : PactType}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hWF : rho.AlphabetWellFormed) (hWFt : theta.AlphabetWellFormed)
    (hOwn : PactType.ParallelMessageOwnership rho)
    (hOwnT : PactType.ParallelMessageOwnership theta)
    (hTail : rho.TailRecursive) (hTailT : theta.TailRecursive)
    (hLive : LiveEq rho theta)
    (hStep : DecoratedTypeTransition env theta label offers theta') :
    ∃ rho', DecoratedTypeTransition env rho label offers rho' ∧
      LiveEqBody theta' rho' :=
  liveEq_decorated_forward hWFt hWF hOwnT hOwn hTailT hTail (liveEq_symm hLive) hStep

end PactType

end Pact
