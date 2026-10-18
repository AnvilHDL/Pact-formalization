import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.OwnershipTransport
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.SurvivorTransport

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

/-- Tail substitution leaves parallel operands unchanged. -/
theorem PactType.replaceVar_parallelMessageOwnership (name : String)
    (replacement : PactType) :
    ∀ processType : PactType,
      processType.ParallelMessageOwnership →
      processType.TailOccurrences name True →
      replacement.ParallelMessageOwnership →
      (processType.replaceVar name replacement).ParallelMessageOwnership := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.ParallelMessageOwnershipBodies branches →
          PactType.TailBranchOccurrences name True branches →
          replacement.ParallelMessageOwnership →
          PactType.ParallelMessageOwnershipBodies
            (PactType.replaceBranches branches name replacement) := by
        intro branches hBranchesSize hOwn hTail hReplacement
        induction branches with
        | nil => simp [PactType.replaceBranches,
            PactType.ParallelMessageOwnershipBodies]
        | cons head rest restIH =>
            rcases head with ⟨action, body⟩
            simp only [PactType.ParallelMessageOwnershipBodies] at hOwn
            simp only [PactType.TailBranchOccurrences] at hTail
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf
                omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: rest) := by
                simp_wf
                omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, body) :: rest) := by
                simp_wf
                omega
              omega
            simp only [PactType.replaceBranches,
              PactType.ParallelMessageOwnershipBodies]
            exact ⟨ih (sizeOf body) hBodySize body rfl hOwn.1 hTail.1
                hReplacement,
              restIH hRestSize hOwn.2 hTail.2⟩
      intro hOwn hTail hReplacement
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          simp [PactType.replaceVar, PactType.ParallelMessageOwnership]
      | var alphabet current =>
          by_cases hName : name = current
          · simpa [PactType.replaceVar, hName] using hReplacement
          · simp [PactType.replaceVar, hName, PactType.ParallelMessageOwnership]
      | recur alphabet current body =>
          by_cases hName : name = current
          · simpa [PactType.replaceVar, hName] using hOwn
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]
              simp_wf
              omega
            simp only [PactType.ParallelMessageOwnership] at hOwn
            simp only [PactType.TailOccurrences,
              if_neg (fun h : current = name => hName h.symm)] at hTail
            simp only [PactType.replaceVar, if_neg hName,
              PactType.ParallelMessageOwnership]
            exact ih (sizeOf body) hBodySize body rfl hOwn hTail hReplacement
      | choice alphabet left right | fairChoice alphabet _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ParallelMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ParallelMessageOwnership]
          exact ⟨ih (sizeOf left) hLeftSize left rfl hOwn.1 hTail.1
              hReplacement,
            ih (sizeOf right) hRightSize right rfl hOwn.2 hTail.2
              hReplacement⟩
      | seq alphabet left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ParallelMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ParallelMessageOwnership]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1]
          exact ⟨hOwn.1,
            ih (sizeOf right) hRightSize right rfl hOwn.2 hTail.2
              hReplacement⟩
      | par alphabet left right interface =>
          simp only [PactType.ParallelMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ParallelMessageOwnership]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement left hTail.1,
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement right hTail.2]
          exact hOwn
      | xoffer alphabet elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.ParallelMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ParallelMessageOwnership]
          exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hOwn.1 hTail.1
              hReplacement,
            hBranches branches hBranchesSize hOwn.2 hTail.2 hReplacement⟩
      | offer alphabet elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.ParallelMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ParallelMessageOwnership]
          rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
            name replacement branches hTail.2]
          exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hOwn.1 hTail.1
              hReplacement,
            hOwn.2⟩

/-- Every represented residual retains the source's parallel ownership. -/
theorem relationMembership_parallelMessageOwnership :
    ∀ (source : PactType) {bound : List String} (residual : PactType)
      (state : TypeAutomatonState),
      TypeWellFormedIn bound source →
      relationMembership (buildRelationSet source (compileType source)) residual state →
      residual.ParallelMessageOwnership := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
    intro bound residual state hWF hRelated
    have hOwn := hWF.2.2.2.2.2.2.2.2.2.1
    cases source with
    | skip alphabet =>
      rw [(relationMembership_skip_cases alphabet hRelated).1]
      exact hOwn
    | var alphabet name =>
      rw [(relationMembership_var_cases alphabet name hRelated).1]
      exact hOwn
    | message alphabet msg dir =>
      rcases relationMembership_message_cases alphabet msg dir hRelated with hRoot | hFinal
      · rw [hRoot.1]; exact hOwn
      · rw [hFinal.1]; simp [PactType.ParallelMessageOwnership]
    | tock alphabet =>
      rcases relationMembership_tock_cases alphabet hRelated with hRoot | hFinal
      · rw [hRoot.1]; exact hOwn
      · rw [hFinal.1]; simp [PactType.ParallelMessageOwnership]
    | progress alphabet pid =>
      rcases relationMembership_progress_cases alphabet pid hRelated with hRoot | hFinal
      · rw [hRoot.1]; exact hOwn
      · rw [hFinal.1]; simp [PactType.ParallelMessageOwnership]
    | choice alphabet left right =>
      obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_choice hWF
      have hLF : typeCompilationFuel left < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      have hRF : typeCompilationFuel right < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      rcases relationMembership_choice_cases alphabet left right hRelated with
        hRoot | ⟨q, _, hL⟩ | ⟨q, _, hR⟩
      · cases hRoot; exact hOwn
      · exact ih _ hLF left rfl residual q hLWF hL
      · exact ih _ hRF right rfl residual q hRWF hR
    | fairChoice alphabet bid left right =>
      obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_fairChoice hWF
      have hLF : typeCompilationFuel left < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      have hRF : typeCompilationFuel right < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
        hRoot | ⟨q, _, hL⟩ | ⟨q, _, hR⟩
      · cases hRoot; exact hOwn
      · exact ih _ hLF left rfl residual q hLWF hL
      · exact ih _ hRF right rfl residual q hRWF hR
    | seq alphabet left right =>
      obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_seq hWF
      have hLF : typeCompilationFuel left < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      have hRF : typeCompilationFuel right < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      rcases relationMembership_seq_cases alphabet left right hRelated with
        ⟨q, rho, hEntry, hL, _⟩ | ⟨q, _, hR⟩
      · cases hEntry
        simp only [PactType.ParallelMessageOwnership] at hOwn ⊢
        exact ⟨ih _ hLF left rfl rho q hLWF hL, hOwn.2⟩
      · exact ih _ hRF right rfl residual q hRWF hR
    | par alphabet left right interface =>
      obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
      obtain ⟨hSLWF, hSRWF⟩ := typeWellFormedIn_survivor hWF
      have hLF : typeCompilationFuel left < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      have hRF : typeCompilationFuel right < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      simp only [PactType.ParallelMessageOwnership] at hOwn
      rcases relationMembership_par_cases alphabet left right interface hRelated with
        ⟨qL, qR, rhoL, rhoR, hEntry, hL, hR⟩ |
        ⟨q, rho, hEntry, hL, _⟩ | ⟨q, rho, hEntry, hR, _⟩ | hFinal
      · cases hEntry
        simp only [PactType.ParallelMessageOwnership]
        refine ⟨?_, ih _ hLF left rfl rhoL qL hLWF hL,
          ih _ hRF right rfl rhoR qR hRWF hR⟩
        intro msg hMsg
        exact hOwn.1 (Finset.mem_inter.mpr
          ⟨(relationMembership_ownership_subset left rhoL qL hL).2.2.2.1
              (Finset.mem_inter.mp hMsg).1,
            (relationMembership_ownership_subset right rhoR qR hR).2.2.2.1
              (Finset.mem_inter.mp hMsg).2⟩)
      · cases hEntry
        exact ih _ (by simpa only [typeCompilationFuel_reannotate] using hLF)
          (left.reannotate alphabet) rfl _ q hSLWF hL
      · cases hEntry
        exact ih _ (by simpa only [typeCompilationFuel_reannotate] using hRF)
          (right.reannotate alphabet) rfl _ q hSRWF hR
      · cases hFinal; simp [PactType.ParallelMessageOwnership]
    | recur alphabet name body =>
      have hBodyWF := typeWellFormedIn_recur hWF
      have hBF : typeCompilationFuel body < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      rcases relationMembership_recur_cases alphabet name body hRelated with
        hRoot | ⟨q, rho, hEntry, hBody⟩
      · cases hRoot; exact hOwn
      · cases hEntry
        have hTailRec := hWF.2.2.2.2.2.1
        simp only [PactType.TailRecursive] at hTailRec
        exact PactType.replaceVar_parallelMessageOwnership name (.recur alphabet name body)
          rho (ih _ hBF body rfl rho q hBodyWF hBody)
          (relationMembership_tailOccurrences body rho q name True
            hTailRec.2 hTailRec.1 hBody) hOwn
    | xoffer alphabet elseType branches =>
      obtain ⟨hElseWF, hBranchWF⟩ := typeWellFormedIn_xoffer hWF
      have hEF : typeCompilationFuel elseType < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      rcases relationMembership_xoffer_cases alphabet elseType branches hRelated with
        hRoot | ⟨q, _, hElse⟩ | ⟨i, action, branch, q, hGet, _, hBranch⟩
      · cases hRoot; exact hOwn
      · exact ih _ hEF elseType rfl residual q hElseWF hElse
      · have hMember := List.mem_of_getElem? hGet
        have hBF : typeCompilationFuel branch < n := by
          have hLe := typeCompilationFuel_le_typeBranchCompilationFuel branches
            (action, branch) hMember
          dsimp only at hLe
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        exact ih _ hBF branch rfl residual q (hBranchWF _ hMember) hBranch
    | offer alphabet elseType branches =>
      obtain ⟨hElseWF, hSelectedWF⟩ := typeWellFormedIn_offer hWF
      have hEF : typeCompilationFuel elseType < n := by
        rw [← hFuel]; simp only [typeCompilationFuel]; omega
      rcases relationMembership_offer_cases alphabet elseType branches hRelated with
        hRoot | ⟨q, _, hElse⟩ | ⟨i, selected, q, hGet, _, hSelected⟩
      · cases hRoot; exact hOwn
      · exact ih _ hEF elseType rfl residual q hElseWF hElse
      · have hSF : typeCompilationFuel
            (parallelTypeBranchesFiring alphabet selected branches) < n := by
          rw [← hFuel]
          exact typeCompilationFuel_firing_lt_offer alphabet elseType selected branches
        exact ih _ hSF (parallelTypeBranchesFiring alphabet selected branches) rfl
          residual q (hSelectedWF _ (Finset.mem_toList.mp (List.mem_of_getElem? hGet))) hSelected

/-- An optimistic menu mentions only names present in the source syntax. -/
theorem typeFutureOffersFuel_messageIds (fuel : Nat) (rho : PactType) :
    ∀ action ∈ typeFutureOffersFuel fuel rho, action.1 ∈ rho.MessageIds := by
  induction fuel generalizing rho with
  | zero => simp [typeFutureOffersFuel]
  | succ fuel ih =>
    have hBranches (branches : List (BareMessage × PactType))
        (initial : Finset BareMessage) (names : Finset MessageId)
        (hInitial : ∀ a ∈ initial, a.1 ∈ names) :
        ∀ a ∈ branches.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2) initial,
          a.1 ∈ names ∪ PactType.BranchMessageIds branches := by
      induction branches generalizing initial names with
      | nil => simpa [PactType.BranchMessageIds] using hInitial
      | cons branch rest ihRest =>
        have hNext : ∀ a ∈ initial ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2,
            a.1 ∈ names ∪ ({branch.1.1} ∪ branch.2.MessageIds) := by
          intro a ha
          rcases Finset.mem_union.mp ha with ha | ha
          · rcases Finset.mem_union.mp ha with ha | ha
            · exact Finset.mem_union_left _ (hInitial a ha)
            · obtain rfl := Finset.mem_singleton.mp ha
              simp
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ (ih _ a ha))
        have hRest := ihRest _ _ hNext
        rcases branch with ⟨action, branchType⟩
        simpa [PactType.BranchMessageIds, Finset.union_assoc] using hRest
    cases rho <;>
      simp only [typeFutureOffersFuel, PactType.MessageIds]
    all_goals try { simp; done }
    case message alphabet msg dir =>
      split <;> simp_all
    case recur alphabet name body => exact ih body
    case choice alphabet left right =>
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.mem_union_left _ (ih _ a ha)
      · exact Finset.mem_union_right _ (ih _ a ha)
    case fairChoice alphabet bid left right =>
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.mem_union_left _ (ih _ a ha)
      · exact Finset.mem_union_right _ (ih _ a ha)
    case seq alphabet left right =>
      split
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact Finset.mem_union_left _ (ih _ a ha)
        · exact Finset.mem_union_right _ (ih _ a ha)
      · intro a ha; exact Finset.mem_union_left _ (ih _ a ha)
    case par alphabet left right interface =>
      intro a ha
      rcases Finset.mem_union.mp (Finset.mem_filter.mp ha).1 with ha | ha
      · exact Finset.mem_union_left _ (ih _ a ha)
      · exact Finset.mem_union_right _ (ih _ a ha)
    case xoffer alphabet elseType branches =>
      intro a ha
      exact hBranches branches _ _ (ih elseType) a (Finset.mem_inter.mp ha).1
    case offer alphabet elseType branches =>
      intro a ha
      exact hBranches branches _ _ (ih elseType) a (Finset.mem_inter.mp ha).1

theorem typeFutureOffers_messageIds (rho : PactType) :
    ∀ action ∈ typeFutureOffers rho, action.1 ∈ rho.MessageIds :=
  typeFutureOffersFuel_messageIds _ rho

private theorem branchHeads_messageIds (branches : List (BareMessage × PactType)) :
    ∀ action ∈ typeBranchActions branches,
      action.1 ∈ PactType.BranchMessageIds branches := by
  intro action hAction
  obtain ⟨branch, hBranch, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hAction)
  exact branch_subset_branchMessageIds hBranch
    (Finset.mem_union_left _ (Finset.mem_singleton_self _))

/-- Both fields of a step use names from its source, including stored child fields. -/
theorem TypeOffers.offers_messageIds {env : TypeEnvironment} {rho rho' : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (h : TypeOffers env rho label rho' current future) :
    (∀ a ∈ current, a.1 ∈ rho.MessageIds) ∧
      (∀ a ∈ future, a.1 ∈ rho.MessageIds) := by
  induction h using TypeOffers.rec with
  | recur env alphabet name body hEnv =>
    refine ⟨by simp, ?_⟩
    intro a ha
    have hm := (replaceVar_ownership_subset name (.recur alphabet name body) body).2.2.2.1
      (typeFutureOffers_messageIds _ a ha)
    simpa [PactType.MessageIds] using hm
  | offer_some env alphabet elseType branches enabled hEnv =>
    simp only [PactType.MessageIds]
    constructor
    · intro a ha
      exact Finset.mem_union_right _
        (branchHeads_messageIds branches a (Finset.mem_inter.mp ha).1)
    · intro a ha
      have hm := typeFutureOffers_messageIds _ a (Finset.mem_sdiff.mp ha).1
      exact Finset.mem_union_right _
        ((parallelTypeBranchesFiringFrom_ownership alphabet enabled branches 0).1 hm)
  | action => simp [PactType.MessageIds, typeFutureOffers, typeFutureOffersFuel]
  | action_wait =>
    constructor
    · simp [PactType.MessageIds]
    · intro a ha
      simpa only [PactType.MessageIds] using
        typeFutureOffers_messageIds _ a (Finset.mem_sdiff.mp ha).1
  | choice_left | choice_right | fair_left | fair_right =>
    exact ⟨by simp, typeFutureOffers_messageIds _⟩
  | cycle | seq_tock | seq_fuse_tock | par_fuse_tock => simp
  | cycle_wait | skip | progress =>
    simp [typeFutureOffers, typeFutureOffersFuel]
  | xoffer_branch env alphabet elseType branches action processType hEnv =>
    simp only [PactType.MessageIds]
    refine ⟨?_, ?_⟩
    · intro a ha
      obtain rfl := Finset.mem_singleton.mp ha
      exact Finset.mem_union_right _ (branch_subset_branchMessageIds hEnv.2.1
        (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
    · intro a ha
      simpa only [PactType.MessageIds] using
        typeFutureOffers_messageIds _ a (Finset.mem_sdiff.mp ha).1
  | xoffer_else env alphabet elseType branches hEnv =>
    refine ⟨?_, fun a ha => typeFutureOffers_messageIds _ a (Finset.mem_sdiff.mp ha).1⟩
    intro a ha
    simpa only [PactType.MessageIds] using Finset.mem_union_right elseType.MessageIds
      (branchHeads_messageIds branches a (Finset.mem_inter.mp ha).1)
  | xoffer_wait env alphabet elseType branches hEnv =>
    simp only [PactType.MessageIds]
    constructor
    · intro a ha
      exact Finset.mem_union_right _ (branchHeads_messageIds branches a
        (Finset.mem_inter.mp ha).2)
    · intro a ha
      simpa only [PactType.MessageIds] using
        typeFutureOffers_messageIds _ a (Finset.mem_sdiff.mp ha).1
  | offer_else env alphabet elseType branches hEnv =>
    simp only [PactType.MessageIds]
    exact ⟨fun a ha => Finset.mem_union_right _ (branchHeads_messageIds _ a (Finset.mem_inter.mp ha).1),
      fun a ha => Finset.mem_union_left _
        (typeFutureOffers_messageIds _ a (Finset.mem_sdiff.mp ha).1)⟩
  | offer_wait env alphabet elseType branches hEnv =>
    simp only [PactType.MessageIds]
    refine ⟨fun a ha => Finset.mem_union_right _ (branchHeads_messageIds _ a (Finset.mem_inter.mp ha).1), ?_⟩
    intro a ha
    simpa only [PactType.MessageIds] using
      typeFutureOffers_messageIds _ a (Finset.mem_sdiff.mp ha).1
  | seq env alphabet left left' right label current childFuture hStep hNotSkip hClock ih
  | seq_fuse env alphabet skipAlphabet left right label current childFuture hStep hClock ih =>
    simp only [PactType.MessageIds]
    refine ⟨fun a ha => Finset.mem_union_left _ (ih.1 a ha), ?_⟩
    intro a ha
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp ha).1 with ha | ha
    · exact Finset.mem_union_left _ (ih.2 a ha)
    · unfold sequenceRightMenu at ha
      split at ha
      · exact Finset.mem_union_right _ (typeFutureOffers_messageIds _ a ha)
      · simp at ha
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ _ _ _ _ ihL ihR =>
    simp only [PactType.MessageIds]
    constructor
    · intro a ha
      rcases Finset.mem_union.mp (Finset.mem_filter.mp ha).1 with ha | ha
      · exact Finset.mem_union_left _ (ihL.1 a ha)
      · exact Finset.mem_union_right _ (ihR.1 a ha)
    · intro a ha
      split at ha
      · simp at ha
      · rcases Finset.mem_union.mp (Finset.mem_filter.mp ha).1 with ha | ha
        · exact Finset.mem_union_left _ (ihL.2 a ha)
        · exact Finset.mem_union_right _ (ihR.2 a ha)
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihL ihR =>
    simp only [PactType.MessageIds]
    constructor
    · intro a ha
      rcases Finset.mem_union.mp (Finset.mem_filter.mp ha).1 with ha | ha
      · exact Finset.mem_union_left _ (ihL.1 a ha)
      · exact Finset.mem_union_right _ (ihR.1 a ha)
    · intro a ha
      rcases Finset.mem_union.mp (Finset.mem_filter.mp ha).1 with ha | ha
      · exact Finset.mem_union_left _ (ihL.2 a ha)
      · exact Finset.mem_union_right _ (ihR.2 a ha)
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [PactType.MessageIds]
    exact ⟨fun a ha => Finset.mem_union_right _ (ih.1 a (Finset.mem_filter.mp ha).1),
      fun a ha => Finset.mem_union_right _ (ih.2 a (Finset.mem_filter.mp ha).1)⟩
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [PactType.MessageIds]
    exact ⟨fun a ha => Finset.mem_union_left _ (ih.1 a (Finset.mem_filter.mp ha).1),
      fun a ha => Finset.mem_union_left _ (ih.2 a (Finset.mem_filter.mp ha).1)⟩

private theorem hidden_union_disjoint {left right : PactType} {interface : Interface}
    {cL fL cR fR : Finset BareMessage}
    (hOwn : left.MessageIds ∩ right.MessageIds ⊆ interface)
    (hL : (∀ a ∈ cL, a.1 ∈ left.MessageIds) ∧
      (∀ a ∈ fL, a.1 ∈ left.MessageIds))
    (hR : (∀ a ∈ cR, a.1 ∈ right.MessageIds) ∧
      (∀ a ∈ fR, a.1 ∈ right.MessageIds))
    (hDL : Disjoint cL fL) (hDR : Disjoint cR fR) :
    Disjoint (hideTypeOffers interface (cL ∪ cR))
      (hideTypeOffers interface (fL ∪ fR)) := by
  apply Finset.disjoint_left.mpr
  intro a hC hF
  obtain ⟨hC, hOutside⟩ := Finset.mem_filter.mp hC
  obtain ⟨hF, _⟩ := Finset.mem_filter.mp hF
  rcases Finset.mem_union.mp hC with hC | hC <;>
    rcases Finset.mem_union.mp hF with hF | hF
  · exact Finset.disjoint_left.mp hDL hC hF
  · exact hOutside (hOwn (Finset.mem_inter.mpr ⟨hL.1 a hC, hR.2 a hF⟩))
  · exact hOutside (hOwn (Finset.mem_inter.mpr ⟨hL.2 a hF, hR.1 a hC⟩))
  · exact Finset.disjoint_left.mp hDR hC hF

/-- Ownership excludes cross-component overlap after interface hiding. -/
theorem TypeOffers.offers_disjoint {env : TypeEnvironment} {rho rho' : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (h : TypeOffers env rho label rho' current future) :
    rho.ParallelMessageOwnership → Disjoint current future := by
  induction h using TypeOffers.rec with
  | action => simp [typeFutureOffers, typeFutureOffersFuel]
  | action_wait | seq | seq_fuse | xoffer_wait | offer_else | offer_wait | offer_some =>
    intro _; exact Finset.sdiff_disjoint.symm
  | choice_left | choice_right | fair_left | fair_right | cycle | cycle_wait
  | skip | progress | recur | seq_tock | seq_fuse_tock
  | par_fuse_tock => simp
  | xoffer_else =>
    intro _
    exact Finset.disjoint_left.mpr fun _ ha hf =>
      (Finset.mem_sdiff.mp hf).2 (Finset.mem_inter.mp ha).1
  | xoffer_branch env alphabet elseType branches action processType hEnv =>
    intro _
    apply Finset.disjoint_left.mpr
    intro a ha hf
    obtain rfl := Finset.mem_singleton.mp ha
    exact (Finset.mem_sdiff.mp hf).2
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨(a, processType), hEnv.2.1, rfl⟩))
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture _ _ hL hR _ _ _ _ ihL ihR =>
    intro hOwn
    simp only [PactType.ParallelMessageOwnership] at hOwn
    split
    · exact Finset.disjoint_empty_right _
    · exact hidden_union_disjoint hOwn.1 hL.offers_messageIds hR.offers_messageIds
        (ihL hOwn.2.1) (ihR hOwn.2.2)
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ hL hR _ _ _ _ ihL ihR =>
    intro hOwn
    simp only [PactType.ParallelMessageOwnership] at hOwn
    exact hidden_union_disjoint hOwn.1 hL.offers_messageIds hR.offers_messageIds
      (ihL hOwn.2.1) (ihR hOwn.2.2)
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro hOwn
    simp only [PactType.ParallelMessageOwnership] at hOwn
    exact Finset.disjoint_left.mpr fun _ hC hF =>
      Finset.disjoint_left.mp (ih hOwn.2.2)
        (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hF).1
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro hOwn
    simp only [PactType.ParallelMessageOwnership] at hOwn
    exact Finset.disjoint_left.mpr fun _ hC hF =>
      Finset.disjoint_left.mp (ih hOwn.2.1)
        (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hF).1

end

end Pact
