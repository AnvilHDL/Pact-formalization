import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.RecursionFuture
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.RecursionMenus
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.MarkerCorrespondence
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Sequence
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.ParallelMenus

/-! Full decorated-step correspondence and menu agreement by constructor induction. -/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

open PendingAutomaton

/-- Well-formed types satisfy decorated-step correspondence and menu agreement. -/
theorem correspondence_simultaneous :
    ∀ (bound : List String) (processType : PactType),
      TypeWellFormedIn bound processType →
      TypeAutomatonStepCorrespondence processType ∧
        FutureOffersAgree processType := by
  intro bound processType
  induction hFuel : typeCompilationFuel processType
      using Nat.strong_induction_on generalizing bound processType with
  | _ n ih =>
    intro hWF
    cases processType with
    | skip alphabet =>
        exact ⟨offerCorrespondence_skip alphabet,
          futureOffersAgree_skip alphabet⟩
    | var alphabet name =>
        exact ⟨offerCorrespondence_var alphabet name,
          futureOffersAgree_var alphabet name⟩
    | message alphabet msg dir =>
        exact ⟨offerCorrespondence_message alphabet msg dir,
          futureOffersAgree_message alphabet msg dir⟩
    | tock alphabet =>
        exact ⟨offerCorrespondence_tock alphabet,
          futureOffersAgree_tock alphabet⟩
    | progress alphabet pid =>
        exact ⟨offerCorrespondence_progress alphabet pid,
          futureOffersAgree_progress alphabet pid⟩
    | choice alphabet left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_choice hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        have hMenus : FutureOffersAgree (.choice alphabet left right) := by
          exact futureOffersAgree_choice alphabet left right
            (offerBranchesDisjoint_of_wellFormedIn hLeftWF)
            (offerBranchesDisjoint_of_wellFormedIn hRightWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2 hRight.2
        refine ⟨?_, hMenus⟩
        exact offerCorrespondence_choice alphabet left right hWF.1
            (offerBranchesDisjoint_of_wellFormedIn hLeftWF)
            (offerBranchesDisjoint_of_wellFormedIn hRightWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.2.1]; rfl)
            hMenus hLeft.1 hRight.1
    | fairChoice alphabet bid left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_fairChoice hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        have hMenus : FutureOffersAgree (.fairChoice alphabet bid left right) := by
          exact futureOffersAgree_fairChoice alphabet bid left right
            (offerBranchesDisjoint_of_wellFormedIn hLeftWF)
            (offerBranchesDisjoint_of_wellFormedIn hRightWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2 hRight.2
        refine ⟨?_, hMenus⟩
        exact offerCorrespondence_fairChoice alphabet bid left right
            hWF.1
            (offerBranchesDisjoint_of_wellFormedIn hLeftWF)
            (offerBranchesDisjoint_of_wellFormedIn hRightWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.2.1]; rfl)
            hMenus hLeft.1 hRight.1
    | seq alphabet left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_seq hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, ?_⟩
        · exact offerCorrespondence_seq alphabet left right
            (fun hRel =>
              relationMembership_alphabetWellFormed
                committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
                left _ _ hLeftWF.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.1
                hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                hLeftWF.2.2.2.2.2.1
                (offerBranchesDisjoint_of_wellFormedIn hLeftWF)
                hRel)
            (offerBranchesDisjoint_of_wellFormedIn hRightWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hRight.2 hLeft.1 hRight.1
        · apply futureOffersAgree_seq alphabet left right
            (offerBranchesDisjoint_of_wellFormedIn hLeftWF)
            (offerBranchesDisjoint_of_wellFormedIn hRightWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2 hRight.2 hLeft.1.toCurrent hLeftWF
          intro name
          have hTail := hWF.2.2.2.1 name
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.1
    | par alphabet left right interface =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_par hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeftResignFuel :
            typeCompilationFuel (left.reannotate alphabet) < n := by
          rw [typeCompilationFuel_reannotate]; exact hLeftFuel
        have hRightResignFuel :
            typeCompilationFuel (right.reannotate alphabet) < n := by
          rw [typeCompilationFuel_reannotate]; exact hRightFuel
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        obtain ⟨hLeftResignWF, hRightResignWF⟩ := typeWellFormedIn_survivor hWF
        have hLeftResign :=
          ih _ hLeftResignFuel bound (left.reannotate alphabet) rfl hLeftResignWF
        have hRightResign :=
          ih _ hRightResignFuel bound (right.reannotate alphabet) rfl
            hRightResignWF
        refine ⟨?_, ?_⟩
        · exact offerCorrespondence_par hWF hLeft.1 hRight.1
            hLeftResign.1 hRightResign.1
        · exact futureOffersAgree_par_of_typeWF hWF hLeft.1.toCurrent hRight.1.toCurrent
            hLeft.2 hRight.2 hLeftResign.2 hRightResign.2
    | recur alphabet name body =>
        have hBodyWF := typeWellFormedIn_recur hWF
        have hBodyFuel : typeCompilationFuel body < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hBody := ih _ hBodyFuel (name :: bound) body rfl hBodyWF
        have hMenus : FutureOffersAgree (.recur alphabet name body) := by
          intro residual state hRelated
          have hAlphabet : body.alphabet = alphabet := by
            have h := hWF.1
            simp only [PactType.AlphabetWellFormed] at h
            exact h.2.1
          have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hBodyWF
          have hTail := hBodyWF.2.2.2.1
          rcases relationMembership_recur_cases alphabet name body hRelated with
            hRoot | ⟨q, rho, hPair, hChildRelated⟩
          · cases hRoot
            -- Paper: the fresh root reads the body-entry menu.
            exact futureOffersAgree_recur_root alphabet name body hAlphabet
              hDisjoint hTail hBody.1.toCurrent hBody.2
          · cases hPair
            -- Paper: installed backedges add the body menu at marker-reachable states.
            rw [computeFutureOf_recur_child_eq alphabet name body hAlphabet
              hDisjoint hTail hBody.1.toCurrent hBody.2 hChildRelated]
            have hRhoTail := relationMembership_tailOccurrences body rho q name True
              hBodyWF.2.2.2.2.2.1 (hTail name) hChildRelated
            have hRhoWF := relationMembership_alphabetWellFormed
              committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
              body rho q hBodyWF.1 hBodyWF.2.2.2.2.2.2.2.2.2.2.2.2.1
              hBodyWF.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              hBodyWF.2.2.2.2.2.1 hDisjoint hChildRelated
            have hRhoAlphabet := relationMembership_alphabet_eq_of_wellFormed
              body rho q hBodyWF.1 hChildRelated
            -- Paper: substitution adds the body menu exactly when b_X holds.
            rw [typeFutureOffers_replaceVar_tail name (.recur alphabet name body)
              rho hRhoTail hRhoWF (by
                rw [hRhoAlphabet, typeFutureOffers_recur]
                exact typeFutureOffers_subset_alphabet body hBodyWF.1),
              typeFutureOffers_recur]
            have hMarker :
                (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable q,
                  MarkerSource (compileTypeFuel (typeCompilationFuel body) body) name reached) ↔
                menuReachesVar name rho = true := by
              -- Paper: M_X agrees with b_X by the smaller-rank marker induction.
              exact markerReachable_iff_menuReachesVar_of_current body (name :: bound) hBodyWF
                (fun child childBound hChildLt hChildWF =>
                  (ih _ (Nat.lt_trans hChildLt hBodyFuel) childBound child rfl hChildWF).1.toCurrent)
                name (List.mem_cons_self) hChildRelated
            simp only [hMarker]
        refine ⟨?_, hMenus⟩
        exact offerCorrespondence_recur alphabet name body hWF hBody.1 hBody.2 hMenus
    | xoffer alphabet elseType branches =>
        obtain ⟨hElseWF, hBranchWF⟩ := typeWellFormedIn_xoffer hWF
        have hElseFuel : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hBranchFuel : ∀ entry ∈ branches,
            typeCompilationFuel entry.2 < n := by
          intro entry hEntry
          rw [← hFuel]
          simp only [typeCompilationFuel]
          have := typeCompilationFuel_le_typeBranchCompilationFuel branches entry
            hEntry
          omega
        have hElse := ih _ hElseFuel bound elseType rfl hElseWF
        have hBranch : ∀ entry ∈ branches,
            TypeAutomatonStepCorrespondence entry.2 ∧
              FutureOffersAgree entry.2 :=
          fun entry hEntry =>
            ih _ (hBranchFuel entry hEntry) bound entry.2 rfl
              (hBranchWF entry hEntry)
        have hMenus : FutureOffersAgree (.xoffer alphabet elseType branches) := by
          exact futureOffersAgree_xoffer alphabet elseType branches
            (offerBranchesDisjoint_of_wellFormedIn hWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (fun branch hMem => by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact PactType.branch_alphabet_eq_of_mem h.2.2.2 hMem)
            hElse.2 (fun branch hMem => (hBranch branch hMem).2)
        refine ⟨?_, hMenus⟩
        refine offerCorrespondence_xoffer alphabet elseType branches
            (offerBranchesDisjoint_of_wellFormedIn hElseWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (fun a t hMem =>
              offerBranchesDisjoint_of_wellFormedIn (hBranchWF (a, t) hMem))
            (fun a t hMem => by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [PactType.branch_alphabet_eq_of_mem h.2.2.2 hMem]; rfl)
            hMenus hElse.1 (fun a t hMem => (hBranch (a, t) hMem).1)
    | offer alphabet elseType branches =>
        have hElseFuel : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hGeneratedFuel : ∀ selected,
            typeCompilationFuel
                (parallelTypeBranchesFiring alphabet selected branches) < n := by
          intro selected
          rw [← hFuel]
          exact typeCompilationFuel_firing_lt_offer alphabet elseType selected branches
        obtain ⟨hElseWF, hSelectedWF⟩ := typeWellFormedIn_offer hWF
        have hElse := ih _ hElseFuel bound elseType rfl hElseWF
        have hSelected : ∀ selected ∈ conjunctiveSelections branches.length,
            TypeAutomatonStepCorrespondence
                (parallelTypeBranchesFiring alphabet selected branches) ∧
              FutureOffersAgree
                (parallelTypeBranchesFiring alphabet selected branches) :=
          fun selected hMem =>
            ih _ (hGeneratedFuel selected) bound _ rfl (hSelectedWF selected hMem)
        have hMenus : FutureOffersAgree (.offer alphabet elseType branches) := by
          refine futureOffersAgree_offer alphabet elseType branches
            (offerBranchesDisjoint_of_wellFormedIn hWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (fun selected _ => parallelTypeBranchesFiring_alphabet alphabet selected branches)
            ?_ ?_ hElse.2 (fun selected hMem => (hSelected selected hMem).2)
          · intro branch hMem
            have h := hWF.1
            simp only [PactType.AlphabetWellFormed] at h
            exact (offerBranchesWellFormed_of_mem h.2.2.2 hMem).1
          · intro branch hMem
            have h := hWF.1
            simp only [PactType.AlphabetWellFormed] at h
            exact (offerBranchesWellFormed_of_mem h.2.2.2 hMem).2
        refine ⟨?_, hMenus⟩
        refine offerCorrespondence_offer alphabet elseType branches
            (offerBranchesDisjoint_of_wellFormedIn hElseWF)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            ?_
            (fun selected hMem =>
              offerBranchesDisjoint_of_wellFormedIn (hSelectedWF selected hMem))
            (fun selected _ => parallelTypeBranchesFiring_alphabet alphabet selected branches)
            hMenus hElse.1 (fun selected hMem => (hSelected selected hMem).1)
        · intro branch hMem
          have hWholeDisjoint :=
            offerBranchesDisjoint_of_wellFormedIn hWF
          simp only [PactType.OfferBranchesDisjoint] at hWholeDisjoint
          exact offerBranchesDisjoint_of_mem_branch hWholeDisjoint.2.2 hMem


end

end Pact
