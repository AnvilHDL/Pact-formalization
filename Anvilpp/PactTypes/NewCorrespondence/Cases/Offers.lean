import Anvilpp.PactTypes.NewCorrespondence.Cases.Parallel

namespace Pact

open Classical
open Pact.NewCorrespondence

noncomputable section

/-- Step correspondence for the worker that partitions an offer alphabet over
its generated singleton components. -/
theorem correspondence_parallelTypeBranchesWithin_stepIff
    (signature : TypeAlphabet) :
    ∀ (alphabet : PactTypeAlphabet)
      (branches : List (BareMessage × PactType)),
      alphabet.WellFormed →
      (∀ branch ∈ branches, branch.1 ∈ alphabet.actions ∧
        branch.2.AlphabetWellFormed ∧
        ∀ targetAlphabet, PactType.ReannotationSafe targetAlphabet branch.2) →
      List.Pairwise (fun b1 b2 => Disjoint
        ({b1.1} ∪ PactType.MessageActions b1.2)
        ({b2.1} ∪ PactType.MessageActions b2.2)) branches →
      (∀ action branchType, (action, branchType) ∈ branches →
        ∀ branchAlphabet,
          StepIffStatement signature
            (branchType.reannotate branchAlphabet)) →
      StepIffStatement signature
        (parallelTypeBranchesWithin alphabet branches) := by
  intro alphabet branches
  induction branches generalizing alphabet with
  | nil =>
      intro _ _ _ _
      change StepIffStatement signature (.skip alphabet)
      exact correspondence_skip_stepIff signature alphabet
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      intro hAlphaWF hBranchesWF hPairwise hBranchesIH
      have hHeadWF := hBranchesWF (action, processType) (by simp)
      cases rest with
      | nil =>
          have hProcessIH : StepIffStatement signature
              (processType.reannotate alphabet) :=
            hBranchesIH action processType (by simp) alphabet
          change StepIffStatement signature
            (.xoffer alphabet (.skip alphabet)
              [(action, processType.reannotate alphabet)])
          exact correspondence_xoffer_stepIff signature alphabet
            (.skip alphabet) [(action, processType.reannotate alphabet)] rfl
            (by intro a t hMem; simpa using
              congrArg PactType.alphabet (congrArg Prod.snd
                (List.mem_singleton.mp hMem)))
            (correspondence_skip_stepIff signature alphabet)
            (by
              intro a t hMem
              have hEq := List.mem_singleton.mp hMem
              cases hEq
              unfold StepIffStatement at hProcessIH ⊢
              intro residual residual' state env label offers hRelated hSymbol
              exact hProcessIH hRelated hSymbol)
      | cons next tail =>
          let leftAlphabet :=
            PactTypeAlphabet.branchPart alphabet (action, processType)
          let rightAlphabet := PactTypeAlphabet.remove alphabet leftAlphabet
          have hLeftAlphaWF : leftAlphabet.WellFormed :=
            PactTypeAlphabet.branchPart_wellFormed hAlphaWF (action, processType)
          have hRightAlphaWF : rightAlphabet.WellFormed :=
            PactTypeAlphabet.remove_wellFormed hAlphaWF
          have hHeadAction : action ∈ leftAlphabet.actions := by
            simp only [leftAlphabet, PactTypeAlphabet.branchPart, Finset.mem_inter]
            exact ⟨hHeadWF.1, Finset.mem_union_left _ (Finset.mem_singleton_self action)⟩
          have hLeftBranchIH : StepIffStatement signature
              (processType.reannotate leftAlphabet) :=
            hBranchesIH action processType (by simp) leftAlphabet
          have hLeftIH : StepIffStatement signature
              (singletonTypeXOfferAt leftAlphabet (action, processType)) := by
            change StepIffStatement signature
              (.xoffer leftAlphabet (.skip leftAlphabet)
                [(action, processType.reannotate leftAlphabet)])
            exact correspondence_xoffer_stepIff signature leftAlphabet
              (.skip leftAlphabet)
              [(action, processType.reannotate leftAlphabet)] rfl
              (by intro a t hMem; simpa using
                congrArg PactType.alphabet (congrArg Prod.snd
                  (List.mem_singleton.mp hMem)))
              (correspondence_skip_stepIff signature leftAlphabet)
              (by
                intro a t hMem
                have hEq := List.mem_singleton.mp hMem
                cases hEq
                unfold StepIffStatement at hLeftBranchIH ⊢
                intro residual residual' state env label offers hRelated hSymbol
                exact hLeftBranchIH hRelated hSymbol)
          rw [List.pairwise_cons] at hPairwise
          obtain ⟨hHeadDisjoint, hTailPairwise⟩ := hPairwise
          have hRestWF : ∀ item ∈ next :: tail, item.1 ∈ rightAlphabet.actions ∧
              item.2.AlphabetWellFormed ∧
              ∀ targetAlphabet, PactType.ReannotationSafe targetAlphabet item.2 :=
            fun item hItem =>
              have hItemBranches := hBranchesWF item (List.mem_cons_of_mem _ hItem)
              ⟨PactTypeAlphabet.mem_remove_branchPart_actions_of_disjoint hItemBranches.1
                  (hHeadDisjoint item hItem),
                hItemBranches.2.1, hItemBranches.2.2⟩
          have hRightIH : StepIffStatement signature
              (parallelTypeBranchesWithin rightAlphabet (next :: tail)) :=
            ih rightAlphabet hRightAlphaWF hRestWF hTailPairwise
              (fun a t hMem branchAlphabet =>
                hBranchesIH a t (by simp [hMem]) branchAlphabet)
          have hLeftWF : (singletonTypeXOfferAt leftAlphabet
              (action, processType)).AlphabetWellFormed :=
            singletonTypeXOfferAt_alphabetWellFormed leftAlphabet hLeftAlphaWF
              hHeadAction hHeadWF.2.1 (hHeadWF.2.2 leftAlphabet)
          have hRightWF : (parallelTypeBranchesWithin rightAlphabet
              (next :: tail)).AlphabetWellFormed :=
            parallelTypeBranchesWithin_alphabet_wellFormed rightAlphabet hRightAlphaWF
              (next :: tail) hTailPairwise hRestWF
          have hCompatible :=
            PactTypeAlphabet.branchPart_remove_parallelCompatible alphabet hAlphaWF
              (action, processType)
          have hParIH : StepIffStatement signature
              (.par alphabet
                (singletonTypeXOfferAt leftAlphabet (action, processType))
                (parallelTypeBranchesWithin rightAlphabet (next :: tail)) ∅) :=
            correspondence_par_stepIff signature alphabet
              (singletonTypeXOfferAt leftAlphabet (action, processType))
              (parallelTypeBranchesWithin rightAlphabet (next :: tail)) ∅
              (by simp)
              (by
                simpa [leftAlphabet, rightAlphabet, singletonTypeXOfferAt]
                  using PactTypeAlphabet.mergeHidden_branchPart_remove_empty
                    alphabet (action, processType))
              (by simpa [leftAlphabet, rightAlphabet, singletonTypeXOfferAt] using hCompatible)
              hLeftWF hRightWF
              (PactType.alphabetCoherent_of_wellFormed _
                (by
                  simp only [PactType.AlphabetWellFormed]
                  refine ⟨hAlphaWF, ?_, hLeftWF, hRightWF⟩
                  simpa [leftAlphabet, rightAlphabet, singletonTypeXOfferAt] using hCompatible))
              hLeftIH hRightIH
          change StepIffStatement signature
            (.par alphabet
              (singletonTypeXOfferAt leftAlphabet (action, processType))
              (parallelTypeBranchesWithin rightAlphabet (next :: tail)) ∅)
          exact hParIH

/-- Step correspondence for the generated, fully unselected branch product. -/
theorem correspondence_parallelTypeBranches_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (hAlphaWF : alphabet.WellFormed)
    (hAlphabetBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hPairwise : List.Pairwise (fun b1 b2 => Disjoint
      ({b1.1} ∪ PactType.MessageActions b1.2)
      ({b2.1} ∪ PactType.MessageActions b2.2)) branches)
    (hSafe : ∀ branch ∈ branches, ∀ targetAlphabet,
      PactType.ReannotationSafe targetAlphabet branch.2)
    (hBranchesIH : ∀ action branchType,
      (action, branchType) ∈ branches → ∀ branchAlphabet,
        StepIffStatement signature (branchType.reannotate branchAlphabet)) :
    StepIffStatement signature (parallelTypeBranches branches) := by
  cases branches with
  | nil =>
      change StepIffStatement signature (.skip PactTypeAlphabet.empty)
      exact correspondence_skip_stepIff signature PactTypeAlphabet.empty
  | cons branch rest =>
      rcases branch with ⟨action, branchType⟩
      have hBranchAlphaEq : branchType.alphabet = alphabet :=
        PactType.branch_alphabet_eq_of_mem (branch := (action, branchType))
          hAlphabetBranches (by simp)
      change StepIffStatement signature
        (parallelTypeBranchesWithin branchType.alphabet ((action, branchType) :: rest))
      rw [hBranchAlphaEq]
      exact correspondence_parallelTypeBranchesWithin_stepIff signature
        alphabet ((action, branchType) :: rest) hAlphaWF
        (fun branch hMem =>
          ⟨branch_action_mem_fixedAlphabet_of_mem hAlphabetBranches hMem,
            branch_body_alphabetWellFormed_of_mem hAlphabetBranches hMem,
            hSafe branch hMem⟩)
        hPairwise hBranchesIH

/-- Step correspondence for the generated branch product after one branch is
selected. -/
theorem correspondence_parallelTypeBranchesSelectingWithin_stepIff
    (signature : TypeAlphabet) :
    ∀ (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
      (branches : List (BareMessage × PactType)),
      selected ∈ branches →
      alphabet.WellFormed →
      (∀ branch ∈ branches, branch.1 ∈ alphabet.actions ∧
        branch.2.AlphabetWellFormed ∧
        ∀ targetAlphabet, PactType.ReannotationSafe targetAlphabet branch.2) →
      List.Pairwise (fun b1 b2 => Disjoint
        ({b1.1} ∪ PactType.MessageActions b1.2)
        ({b2.1} ∪ PactType.MessageActions b2.2)) branches →
      (∀ action branchType, (action, branchType) ∈ branches →
        ∀ branchAlphabet,
          StepIffStatement signature
            (branchType.reannotate branchAlphabet)) →
      StepIffStatement signature
        (parallelTypeBranchesSelectingWithin alphabet selected branches) := by
  intro alphabet selected branches
  induction branches generalizing alphabet with
  | nil =>
      intro hMem
      cases hMem
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      intro hSelected hAlphaWF hBranchesWF hPairwise hBranchesIH
      have hHeadWF := hBranchesWF (action, processType) (by simp)
      cases rest with
      | nil =>
          have hEq : selected = (action, processType) := by simpa using hSelected
          subst selected
          have hHeadBranchIH : StepIffStatement signature
              (processType.reannotate alphabet) :=
            hBranchesIH action processType (by simp) alphabet
          have hSeq : StepIffStatement signature
              (.seq alphabet (.message alphabet action.1 action.2)
                (processType.reannotate alphabet)) :=
            correspondence_seq_stepIff signature alphabet
              (.message alphabet action.1 action.2)
              (processType.reannotate alphabet) rfl
              (PactType.reannotate_alphabet alphabet processType)
              (correspondence_message_stepIff signature alphabet action.1 action.2)
              hHeadBranchIH
          change StepIffStatement signature
            (if (action, processType) = (action, processType) then
              selectedTypeBranchAt alphabet (action, processType)
            else singletonTypeXOfferAt alphabet (action, processType))
          rw [if_pos rfl]
          unfold selectedTypeBranchAt
          exact hSeq
      | cons next tail =>
          let leftAlphabet :=
            PactTypeAlphabet.branchPart alphabet (action, processType)
          let rightAlphabet := PactTypeAlphabet.remove alphabet leftAlphabet
          have hLeftAlphaWF : leftAlphabet.WellFormed :=
            PactTypeAlphabet.branchPart_wellFormed hAlphaWF (action, processType)
          have hRightAlphaWF : rightAlphabet.WellFormed :=
            PactTypeAlphabet.remove_wellFormed hAlphaWF
          have hHeadAction : action ∈ leftAlphabet.actions := by
            simp only [leftAlphabet, PactTypeAlphabet.branchPart, Finset.mem_inter]
            exact ⟨hHeadWF.1, Finset.mem_union_left _ (Finset.mem_singleton_self action)⟩
          rw [List.pairwise_cons] at hPairwise
          obtain ⟨hHeadDisjoint, hTailPairwise⟩ := hPairwise
          have hCompatible :=
            PactTypeAlphabet.branchPart_remove_parallelCompatible alphabet hAlphaWF
              (action, processType)
          have hRestWF : ∀ item ∈ next :: tail, item.1 ∈ rightAlphabet.actions ∧
              item.2.AlphabetWellFormed ∧
              ∀ targetAlphabet, PactType.ReannotationSafe targetAlphabet item.2 :=
            fun item hItem =>
              have hItemBranches := hBranchesWF item (List.mem_cons_of_mem _ hItem)
              ⟨PactTypeAlphabet.mem_remove_branchPart_actions_of_disjoint hItemBranches.1
                  (hHeadDisjoint item hItem),
                hItemBranches.2.1, hItemBranches.2.2⟩
          simp only [parallelTypeBranchesSelectingWithin]
          split
          next hHead =>
            subst selected
            have hLeftIH : StepIffStatement signature
                (selectedTypeBranchAt leftAlphabet (action, processType)) := by
              change StepIffStatement signature
                (.seq leftAlphabet (.message leftAlphabet action.1 action.2)
                  (processType.reannotate leftAlphabet))
              exact correspondence_seq_stepIff signature leftAlphabet
                (.message leftAlphabet action.1 action.2)
                (processType.reannotate leftAlphabet) rfl
                (PactType.reannotate_alphabet leftAlphabet processType)
                (correspondence_message_stepIff signature leftAlphabet
                  action.1 action.2)
                (hBranchesIH action processType (by simp) leftAlphabet)
            have hRightIH : StepIffStatement signature
                (parallelTypeBranchesWithin rightAlphabet (next :: tail)) :=
              correspondence_parallelTypeBranchesWithin_stepIff signature
                rightAlphabet (next :: tail) hRightAlphaWF hRestWF hTailPairwise
                (fun a t hMem branchAlphabet =>
                  hBranchesIH a t (by simp [hMem]) branchAlphabet)
            have hLeftWF : (selectedTypeBranchAt leftAlphabet
                (action, processType)).AlphabetWellFormed :=
              selectedTypeBranchAt_alphabetWellFormed leftAlphabet hLeftAlphaWF
                hHeadAction hHeadWF.2.1 (hHeadWF.2.2 leftAlphabet)
            have hRightWF : (parallelTypeBranchesWithin rightAlphabet
                (next :: tail)).AlphabetWellFormed :=
              parallelTypeBranchesWithin_alphabet_wellFormed rightAlphabet hRightAlphaWF
                (next :: tail) hTailPairwise hRestWF
            have hParIH : StepIffStatement signature
                (.par alphabet
                  (selectedTypeBranchAt leftAlphabet (action, processType))
                  (parallelTypeBranchesWithin rightAlphabet (next :: tail)) ∅) :=
              correspondence_par_stepIff signature alphabet
                (selectedTypeBranchAt leftAlphabet (action, processType))
                (parallelTypeBranchesWithin rightAlphabet (next :: tail)) ∅
                (by simp)
                (by
                  simpa [leftAlphabet, rightAlphabet, selectedTypeBranchAt]
                    using PactTypeAlphabet.mergeHidden_branchPart_remove_empty
                      alphabet (action, processType))
                (by
                  simpa [leftAlphabet, rightAlphabet, selectedTypeBranchAt]
                    using hCompatible)
                hLeftWF hRightWF
                (PactType.alphabetCoherent_of_wellFormed _
                  (by
                    simp only [PactType.AlphabetWellFormed]
                    refine ⟨hAlphaWF, ?_, hLeftWF, hRightWF⟩
                    simpa [leftAlphabet, rightAlphabet, selectedTypeBranchAt]
                      using hCompatible))
                hLeftIH hRightIH
            change StepIffStatement signature
              (.par alphabet
                (selectedTypeBranchAt leftAlphabet (action, processType))
                (parallelTypeBranchesWithin rightAlphabet (next :: tail)) ∅)
            exact hParIH
          next hHead =>
            have hTailMem : selected ∈ next :: tail := by
              simp only [List.mem_cons] at hSelected
              rcases hSelected with hSelected | hSelected
              · exact absurd hSelected.symm hHead
              · simp [List.mem_cons, hSelected]
            have hLeftBranchIH : StepIffStatement signature
                (processType.reannotate leftAlphabet) :=
              hBranchesIH action processType (by simp) leftAlphabet
            have hLeftIH : StepIffStatement signature
                (singletonTypeXOfferAt leftAlphabet (action, processType)) := by
              change StepIffStatement signature
                (.xoffer leftAlphabet (.skip leftAlphabet)
                  [(action, processType.reannotate leftAlphabet)])
              exact correspondence_xoffer_stepIff signature leftAlphabet
                (.skip leftAlphabet)
                [(action, processType.reannotate leftAlphabet)] rfl
                (by intro a t hMem; simpa using
                  congrArg PactType.alphabet (congrArg Prod.snd
                    (List.mem_singleton.mp hMem)))
                (correspondence_skip_stepIff signature leftAlphabet)
                (by
                  intro a t hMem
                  have hEq := List.mem_singleton.mp hMem
                  cases hEq
                  unfold StepIffStatement at hLeftBranchIH ⊢
                  intro residual residual' state env label offers hRelated hSymbol
                  exact hLeftBranchIH hRelated hSymbol)
            have hRightIH : StepIffStatement signature
                (parallelTypeBranchesSelectingWithin rightAlphabet selected
                  (next :: tail)) :=
              ih rightAlphabet hTailMem hRightAlphaWF hRestWF hTailPairwise
                (fun a t hMem branchAlphabet =>
                  hBranchesIH a t (by simp [hMem]) branchAlphabet)
            have hLeftWF : (singletonTypeXOfferAt leftAlphabet
                (action, processType)).AlphabetWellFormed :=
              singletonTypeXOfferAt_alphabetWellFormed leftAlphabet hLeftAlphaWF
                hHeadAction hHeadWF.2.1 (hHeadWF.2.2 leftAlphabet)
            have hRightWF : (parallelTypeBranchesSelectingWithin rightAlphabet selected
                (next :: tail)).AlphabetWellFormed :=
              parallelTypeBranchesSelectingWithin_alphabet_wellFormed rightAlphabet
                hRightAlphaWF selected (next :: tail) hTailPairwise hRestWF
            have hParIH : StepIffStatement signature
                (.par alphabet
                  (singletonTypeXOfferAt leftAlphabet (action, processType))
                  (parallelTypeBranchesSelectingWithin rightAlphabet selected
                    (next :: tail)) ∅) :=
              correspondence_par_stepIff signature alphabet
                (singletonTypeXOfferAt leftAlphabet (action, processType))
                (parallelTypeBranchesSelectingWithin rightAlphabet selected
                  (next :: tail)) ∅ (by simp)
                (by
                  simpa [leftAlphabet, rightAlphabet, singletonTypeXOfferAt]
                    using PactTypeAlphabet.mergeHidden_branchPart_remove_empty
                      alphabet (action, processType))
                (by
                  simpa [leftAlphabet, rightAlphabet, singletonTypeXOfferAt]
                    using hCompatible)
                hLeftWF hRightWF
                (PactType.alphabetCoherent_of_wellFormed _
                  (by
                    simp only [PactType.AlphabetWellFormed]
                    refine ⟨hAlphaWF, ?_, hLeftWF, hRightWF⟩
                    simpa [leftAlphabet, rightAlphabet, singletonTypeXOfferAt]
                      using hCompatible))
                hLeftIH hRightIH
            change StepIffStatement signature
              (.par alphabet
                (singletonTypeXOfferAt leftAlphabet (action, processType))
                (parallelTypeBranchesSelectingWithin rightAlphabet selected
                  (next :: tail)) ∅)
            exact hParIH

/-- Step correspondence for the public selected-branch product. -/
theorem correspondence_parallelTypeBranchesSelecting_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (hAlphaWF : alphabet.WellFormed)
    (hAlphabetBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hPairwise : List.Pairwise (fun b1 b2 => Disjoint
      ({b1.1} ∪ PactType.MessageActions b1.2)
      ({b2.1} ∪ PactType.MessageActions b2.2)) branches)
    (hSafe : ∀ branch ∈ branches, ∀ targetAlphabet,
      PactType.ReannotationSafe targetAlphabet branch.2)
    (hBranchesIH : ∀ action branchType,
      (action, branchType) ∈ branches → ∀ branchAlphabet,
        StepIffStatement signature (branchType.reannotate branchAlphabet))
    (selected : BareMessage × PactType) (hSelected : selected ∈ branches) :
    StepIffStatement signature
      (parallelTypeBranchesSelecting selected branches) := by
  cases branches with
  | nil => cases hSelected
  | cons branch rest =>
      rcases branch with ⟨action, branchType⟩
      have hBranchAlphaEq : branchType.alphabet = alphabet :=
        PactType.branch_alphabet_eq_of_mem (branch := (action, branchType))
          hAlphabetBranches (by simp)
      change StepIffStatement signature
        (parallelTypeBranchesSelectingWithin branchType.alphabet selected
          ((action, branchType) :: rest))
      rw [hBranchAlphaEq]
      exact correspondence_parallelTypeBranchesSelectingWithin_stepIff signature
        alphabet selected ((action, branchType) :: rest) hSelected hAlphaWF
        (fun branch hMem =>
          ⟨branch_action_mem_fixedAlphabet_of_mem hAlphabetBranches hMem,
            branch_body_alphabetWellFormed_of_mem hAlphabetBranches hMem,
            hSafe branch hMem⟩)
        hPairwise hBranchesIH

set_option maxHeartbeats 4000000 in
/-- Step correspondence for conjunctive offer `⋀(τ0,B)`. -/
theorem correspondence_offer_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hAlphaWF : alphabet.WellFormed)
    (hAlphabetBranches :
      PactType.BranchesAlphabetWellFormed alphabet branches)
    (hPairwise : List.Pairwise (fun b1 b2 => Disjoint
      ({b1.1} ∪ PactType.MessageActions b1.2)
      ({b2.1} ∪ PactType.MessageActions b2.2)) branches)
    (hSafe : ∀ branch ∈ branches, ∀ targetAlphabet,
      PactType.ReannotationSafe targetAlphabet branch.2)
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hElseIH : StepIffStatement signature elseType)
    (hBranchesIH :
      ∀ action branchType, (action, branchType) ∈ branches →
        ∀ branchAlphabet,
          StepIffStatement signature
            (branchType.reannotate branchAlphabet)) :
    StepIffStatement signature (.offer alphabet elseType branches) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- A generated branch commit is a finite parallel product already covered
  -- by the exclusive-offer/sequence/parallel cases, so a finite induction
  -- over the branch list gives it a correspondence the way `hElseIH` gives
  -- `τ0`'s. Given this, now we need to prove the root's fire/else/wait edges
  -- match the three offer rules.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabetFor alphabet := by
    simpa [compileType] using hSymbol
  have hElseFuelStrict : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.offer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hBranchFuelStrict : ∀ selected : BareMessage × PactType,
      typeCompilationFuel (parallelTypeBranchesSelecting selected branches) + 1 ≤
        typeCompilationFuel (.offer alphabet elseType branches) := by
    intro selected
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    simp only [typeCompilationFuel]; omega
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.offer alphabet elseType branches))
        (.offer alphabet elseType branches) =
        buildSelectedConjunctiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun selected => (selected.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches))) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show buildSelectedConjunctiveOfferAutomaton signature branches
        (compileTypeFuel signature
          (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)) elseType)
        (branches.map fun selected => (selected.1, compileTypeFuel signature
          (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
          (parallelTypeBranchesSelecting selected branches))) =
      buildSelectedConjunctiveOfferAutomaton signature branches
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
        (branches.map fun selected => (selected.1, compileTypeFuel signature
          (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
          (parallelTypeBranchesSelecting selected branches)))
    congr 1
    · exact compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl
    · apply List.map_congr_left
      intro selected _
      congr 1
      exact compileTypeFuel_eq_of_sufficient signature
        (parallelTypeBranchesSelecting selected branches)
        (by
          show typeCompilationFuel (parallelTypeBranchesSelecting selected branches) ≤
            max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)
          rw [typeCompilationFuel_parallelTypeBranchesSelecting]
          exact le_max_right _ _)
        le_rfl
  have hElseProductInfo : ∀ visited,
      stateProductInfo (.offer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited := by
    intro visited
    unfold stateProductInfo
    rw [hFuelEq]
    simp only [stateProductInfoFuel]
    exact stateProductInfoFuel_eq_of_sufficient elseType visited
      (by
        simp only [TypeCompilationFuelSufficient]
        exact le_max_left _ _)
      (typeCompilationFuel_sufficient elseType)
  have hBranchProductInfo : ∀ i selected,
      branches[i]? = some selected → ∀ visited,
        stateProductInfo (.offer alphabet elseType branches)
            (.child (i + 1) visited) =
          stateProductInfo (parallelTypeBranchesSelecting selected branches)
            visited := by
    intro i selected hSelected visited
    unfold stateProductInfo
    rw [hFuelEq]
    simp only [stateProductInfoFuel, hSelected]
    exact stateProductInfoFuel_eq_of_sufficient
      (parallelTypeBranchesSelecting selected branches) visited
      (by
        simp only [TypeCompilationFuelSufficient]
        rw [typeCompilationFuel_parallelTypeBranchesSelecting]
        exact le_max_right _ _)
      (typeCompilationFuel_sufficient
        (parallelTypeBranchesSelecting selected branches))
  rcases relationMembership_offer_cases signature alphabet elseType branches hRelated with
    hRoot | ⟨q, hStateEq, hElseRelated⟩ |
    ⟨i, selected, q, hSelectedEq, hStateEq, hBranchRelated⟩
  · -- root case: `residual` represents `⋀(τ0,B)` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hFutureElseEq : computeFutureOf signature (.offer alphabet elseType branches)
        (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
          elseType).initial) = typeFutureOffers elseType := by
      rw [computeFutureOf_selectedConjunctiveOffer_else signature elseType branches
        (.offer alphabet elseType branches) hWhole hElseFuelStrict hElseProductInfo
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
          le_rfl)]
      show computeFutureOf signature elseType (compileType signature elseType).initial =
        typeFutureOffers elseType
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial elseType (compileType signature elseType))
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabetFor_environment_mem signature alphabet hSignatureSymbol
    have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
    have hRootRelated : relationMembership
        (buildRelationSet (.offer alphabet elseType branches)
          (compileType signature (.offer alphabet elseType branches)))
        (.offer alphabet elseType branches) TypeAutomatonState.root := by
      simpa using hRelated
    have hRootFuture : computeFutureOf signature (.offer alphabet elseType branches)
        TypeAutomatonState.root = typeFutureOffers (.offer alphabet elseType branches) :=
      helper_h15_future_offers_agree signature hRootRelated
    constructor
    · intro hStep
      obtain ⟨-, hOffers⟩ := hStep
      generalize hLabelEq : label = actualLabel at hOffers
      generalize hTargetEq : residual' = actualTarget at hOffers
      generalize hCurrentEq : current = actualCurrent at hOffers
      generalize hFutureEq : future = actualFuture at hOffers
      cases hOffers with
      | offer_some _ _ _ _ enabled hPremise =>
          obtain ⟨hWF', hEnabledMem, hEnabled⟩ := hPremise
          obtain ⟨index, hSelectedGet⟩ := List.mem_iff_getElem?.mp hEnabledMem
          have hFutureBranchEq : computeFutureOf signature (.offer alphabet elseType branches)
              (.child (index + 1) (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial) =
              typeFutureOffers (parallelTypeBranchesSelecting enabled branches) := by
            rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
              (.offer alphabet elseType branches) hWhole index enabled hSelectedGet
              (hBranchFuelStrict enabled) (hBranchProductInfo index enabled hSelectedGet)
              (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial
              (compileTypeFuel_initial_mem signature (typeCompilationFuel
                (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches) le_rfl)]
            show computeFutureOf signature (parallelTypeBranchesSelecting enabled branches)
              (compileType signature (parallelTypeBranchesSelecting enabled branches)).initial =
              typeFutureOffers (parallelTypeBranchesSelecting enabled branches)
            exact helper_h15_future_offers_agree signature
              (buildRelationSet_initial (parallelTypeBranchesSelecting enabled branches)
                (compileType signature (parallelTypeBranchesSelecting enabled branches)))
          have hSignatureSymbol' :
              TypeAutomatonSymbol.mk env TypeLabel.silent
                (TypeOfferSummary.mk ∅ (typeFutureOffers
                  (parallelTypeBranchesSelecting enabled branches))) ∈
        signature.transitionAlphabetFor alphabet := by
            rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
            exact hSignatureSymbol
          have hEnabledPending :
              ({ source := TypeAutomatonState.root, environment := env,
                  label := AutomatonConstructionLabel.visible TypeLabel.silent,
                  current := (∅ : Finset BareMessage),
                  future := FutureSpec.at (childState (index + 1) (compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                    (parallelTypeBranchesSelecting enabled branches)).initial) ∅,
                  target := childState (index + 1) (compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                    (parallelTypeBranchesSelecting enabled branches)).initial } :
                PendingAutomatonEdge) ∈
                (buildSelectedConjunctiveOfferAutomaton signature branches
                  (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
                  (branches.map fun selected' => (selected'.1, compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
                    (parallelTypeBranchesSelecting selected' branches)))).edges := by
            simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union]
            refine Or.inl (Or.inl (Or.inr ?_))
            rw [mem_foldl_union_iff]
            refine Or.inr ⟨(⟨enabled.1, compileTypeFuel signature
              (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
              (parallelTypeBranchesSelecting enabled branches)⟩, index), ?_, ?_⟩
            · exact List.mk_mem_zipIdx_iff_getElem?.mpr
                ((branches_map_selecting_getElem?_eq_some_iff signature branches index enabled.1
                  (compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                    (parallelTypeBranchesSelecting enabled branches))).mpr
                  ⟨enabled.2, hSelectedGet, rfl⟩)
            · simp only [Finset.mem_image, Finset.mem_filter]
              exact ⟨env, ⟨hEnvMem, hEnabled⟩, rfl⟩
          have hEdgeFact : (compileType signature (.offer alphabet elseType branches)).HasEdge
              TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers
                (parallelTypeBranchesSelecting enabled branches)))
              (.child (index + 1) (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
              TypeAutomatonState.root (.child (index + 1) (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial) env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers
                (parallelTypeBranchesSelecting enabled branches))) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hEnabledPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureBranchEq
          have hEnabledStep : DecoratedTypeTransition env (.offer alphabet elseType branches)
              TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers
                (parallelTypeBranchesSelecting enabled branches)))
              (parallelTypeBranchesSelecting enabled branches) :=
            ⟨TypeTransition.offer_some env alphabet elseType branches enabled
              ⟨hWF, hEnabledMem, hEnabled⟩,
              TypeOffers.offer_some env alphabet elseType branches enabled
                ⟨hWF, hEnabledMem, hEnabled⟩⟩
          refine ⟨.child (index + 1) (compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
            (parallelTypeBranchesSelecting enabled branches)).initial, hEdgeFact, ?_⟩
          exact relationMembership_offer_selected signature alphabet elseType branches hSelectedGet
            (buildRelationSet_initial
              (parallelTypeBranchesSelecting enabled branches)
              (compileType signature (parallelTypeBranchesSelecting enabled branches)))
      | offer_else _ _ _ _ hPremise =>
          obtain ⟨hWF', hClock, hNoImmediate, hResolvedNeeds⟩ := hPremise
          have hSignatureSymbol' :
              TypeAutomatonSymbol.mk env TypeLabel.silent
                (TypeOfferSummary.mk (typeBranchActions branches) (typeFutureOffers elseType)) ∈
                signature.transitionAlphabetFor alphabet := by
            rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
            exact hSignatureSymbol
          have hElsePending :
              ({ source := TypeAutomatonState.root, environment := env,
                  label := AutomatonConstructionLabel.visible TypeLabel.silent,
                  current := typeBranchActions branches,
                  future := FutureSpec.at (childState 0 (compileTypeFuel signature
                    (typeCompilationFuel elseType) elseType).initial) ∅,
                  target := childState 0 (compileTypeFuel signature
                    (typeCompilationFuel elseType) elseType).initial } :
                PendingAutomatonEdge) ∈
                (buildSelectedConjunctiveOfferAutomaton signature branches
                  (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
                  (branches.map fun selected' => (selected'.1, compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
                    (parallelTypeBranchesSelecting selected' branches)))).edges := by
            simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter]
            exact Or.inr ⟨env, ⟨hEnvMem, hClock, hNoImmediate, hResolvedNeeds⟩, rfl⟩
          have hEdgeFact : (compileType signature (.offer alphabet elseType branches)).HasEdge
              TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk (typeBranchActions branches) (typeFutureOffers elseType))
              (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
                elseType).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
              TypeAutomatonState.root (.child 0 (compileTypeFuel signature
                (typeCompilationFuel elseType) elseType).initial) env TypeLabel.silent
              (TypeOfferSummary.mk (typeBranchActions branches) (typeFutureOffers elseType))
              hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hElsePending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureElseEq
          have hElseStep : DecoratedTypeTransition env (.offer alphabet elseType branches)
              TypeLabel.silent (TypeOfferSummary.mk (typeBranchActions branches)
                (typeFutureOffers elseType)) elseType :=
            ⟨TypeTransition.offer_else env alphabet elseType branches
              ⟨hWF, hClock, hNoImmediate, hResolvedNeeds⟩,
              TypeOffers.offer_else env alphabet elseType branches
                ⟨hWF, hClock, hNoImmediate, hResolvedNeeds⟩⟩
          refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
            elseType).initial, hEdgeFact, ?_⟩
          exact relationMembership_offer_else signature alphabet elseType branches
            (buildRelationSet_initial elseType (compileType signature elseType))
      | offer_wait _ _ _ _ hPremise =>
          obtain ⟨hWF', hClock, hNoImmediate, hUnresolved⟩ := hPremise
          have hSignatureSymbol' :
              TypeAutomatonSymbol.mk env TypeLabel.silent
                (TypeOfferSummary.mk (typeWaitingOffers env branches)
                  (typeFutureOffers (.offer alphabet elseType branches) \
                    typeWaitingOffers env branches)) ∈
                signature.transitionAlphabetFor alphabet := by
            rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
            exact hSignatureSymbol
          have hWaitPending :
              ({ source := TypeAutomatonState.root, environment := env,
                  label := AutomatonConstructionLabel.visible TypeLabel.silent,
                  current := typeWaitingOffers env branches,
                  future := FutureSpec.at TypeAutomatonState.root
                    (typeWaitingOffers env branches),
                  target := TypeAutomatonState.root } : PendingAutomatonEdge) ∈
                (buildSelectedConjunctiveOfferAutomaton signature branches
                  (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
                  (branches.map fun selected' => (selected'.1, compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
                    (parallelTypeBranchesSelecting selected' branches)))).edges := by
            simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter]
            refine Or.inl (Or.inr ⟨env, ⟨hEnvMem, hClock, hNoImmediate, hUnresolved⟩, ?_⟩)
            simp [typeWaitingOffers]
          have hEdgeFact : (compileType signature (.offer alphabet elseType branches)).HasEdge
              TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.offer alphabet elseType branches) \
                  typeWaitingOffers env branches)) TypeAutomatonState.root := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
              TypeAutomatonState.root TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.offer alphabet elseType branches) \
                  typeWaitingOffers env branches)) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hWaitPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            show computeFutureOf signature (.offer alphabet elseType branches) TypeAutomatonState.root \
              typeWaitingOffers env branches = typeFutureOffers (.offer alphabet elseType branches) \
                typeWaitingOffers env branches
            rw [hRootFuture]
          have hWaitStep : DecoratedTypeTransition env (.offer alphabet elseType branches)
              TypeLabel.silent (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.offer alphabet elseType branches) \
                  typeWaitingOffers env branches)) (.offer alphabet elseType branches) :=
            ⟨TypeTransition.offer_wait env alphabet elseType branches
              ⟨hWF, hClock, hNoImmediate, hUnresolved⟩,
              TypeOffers.offer_wait env alphabet elseType branches
                ⟨hWF, hClock, hNoImmediate, hUnresolved⟩⟩
          refine ⟨TypeAutomatonState.root, hEdgeFact, ?_⟩
          exact relationMembership_offer_root signature alphabet elseType branches
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer alphabet elseType branches) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.offer alphabet elseType branches) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hRootSource : pendingEdge.source = TypeAutomatonState.root := hPSource
      simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hPendingMem
      rcases hPendingMem with ((((hElse | hIndexed) | hEnabledFamily) | hWait) | hResolved2)
      · exfalso
        simp only [childPendingEdges, Finset.mem_image] at hElse
        obtain ⟨childEdge, _, hEq⟩ := hElse
        rw [← hEq] at hRootSource
        simp [childPendingEdge, childState] at hRootSource
      · exfalso
        rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, _, hNewEdge⟩
        · simp at hEmpty
        · simp only [childPendingEdges, Finset.mem_image] at hNewEdge
          obtain ⟨childEdge, _, hEq⟩ := hNewEdge
          rw [← hEq] at hRootSource
          simp [childPendingEdge, childState] at hRootSource
      · -- fire family: reconstructs `offer_some`
        rw [mem_foldl_union_iff] at hEnabledFamily
        rcases hEnabledFamily with hEmpty | ⟨indexed, hIndexedEntry, hNewEdge⟩
        · simp at hEmpty
        · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
          obtain ⟨⟨branchAction, automaton⟩, index⟩ := indexed
          rcases hNewEdge with ⟨environment, ⟨hEnvMem, hEnabled⟩, rfl⟩
          have hEnvEq : environment = env := hPEnv
          subst environment
          have hIndexedGet :
              (branches.map fun selected' => (selected'.1, compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
                (parallelTypeBranchesSelecting selected' branches)))[index]? =
                some (branchAction, automaton) :=
            List.mk_mem_zipIdx_iff_getElem?.mp hIndexedEntry
          obtain ⟨branchType', hSelectedGet, hAutEq⟩ :=
            (branches_map_selecting_getElem?_eq_some_iff signature branches index branchAction
              automaton).mp hIndexedGet
          have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
          have hEnabledMem : (branchAction, branchType') ∈ branches :=
            List.mem_iff_getElem?.mpr ⟨index, hSelectedGet⟩
          simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
          have hLabelEq : label = TypeLabel.silent := by
            have h := hPLabel; simp at h; exact h.symm
          have hCurrentEq : current = ∅ := hPCurrent.symm
          have hTargetEq : state' = .child (index + 1)
              (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting (branchAction, branchType')
                  branches))
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)).initial := by
            rw [← hPTarget, ← hAutEq]
          rw [hTargetEq] at hTargetRelated
          have hFutureEq : future =
              typeFutureOffers (parallelTypeBranchesSelecting
                (branchAction, branchType') branches) := by
            rw [← hPFuture, Finset.sdiff_empty, ← hAutEq]
            rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
              (.offer alphabet elseType branches) hWhole index (branchAction, branchType') hSelectedGet
              (hBranchFuelStrict (branchAction, branchType'))
              (hBranchProductInfo index (branchAction, branchType') hSelectedGet)
              (compileTypeFuel signature (typeCompilationFuel
                (parallelTypeBranchesSelecting (branchAction, branchType') branches))
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)).initial
              (compileTypeFuel_initial_mem signature (typeCompilationFuel
                (parallelTypeBranchesSelecting (branchAction, branchType') branches))
                (parallelTypeBranchesSelecting (branchAction, branchType') branches) le_rfl)]
            show computeFutureOf signature
              (parallelTypeBranchesSelecting (branchAction, branchType') branches)
              (compileType signature
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)).initial =
              typeFutureOffers (parallelTypeBranchesSelecting
                (branchAction, branchType') branches)
            exact helper_h15_future_offers_agree signature
              (buildRelationSet_initial
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)
                (compileType signature
                  (parallelTypeBranchesSelecting (branchAction, branchType') branches)))
          rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated
            with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
              ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain,
                hBranchRelatedAgain⟩
          · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
          · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
              index + 1) (by omega)
          · have hSndEq : (TypeAutomatonState.child (iAgain + 1) qAgain) =
                .child (index + 1) (compileTypeFuel signature (typeCompilationFuel
                  (parallelTypeBranchesSelecting (branchAction, branchType') branches))
                  (parallelTypeBranchesSelecting (branchAction, branchType')
                    branches)).initial := by
              simpa [childState] using hStateEqAgain.symm
            injection hSndEq with hIEq hQEq
            have hIAgainEq : iAgain = index := by omega
            subst hIAgainEq
            have hPairEq : selectedAgain = (branchAction, branchType') := by
              have h := hSelectedEqAgain.symm.trans hSelectedGet
              simpa using h
            rw [hPairEq, hQEq] at hBranchRelatedAgain
            have hResidualEq : residual' =
                parallelTypeBranchesSelecting (branchAction, branchType') branches :=
              relationMembership_functional
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)
                (compileType signature
                  (parallelTypeBranchesSelecting (branchAction, branchType') branches))
                hBranchRelatedAgain
                (buildRelationSet_initial
                  (parallelTypeBranchesSelecting (branchAction, branchType') branches)
                  (compileType signature
                    (parallelTypeBranchesSelecting (branchAction, branchType') branches)))
            rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
            exact ⟨TypeTransition.offer_some env alphabet elseType branches
              (branchAction, branchType')
              ⟨hWF, hEnabledMem, hEnabled⟩,
              TypeOffers.offer_some env alphabet elseType branches
                (branchAction, branchType')
                ⟨hWF, hEnabledMem, hEnabled⟩⟩
      · -- wait family: reconstructs `offer_wait`
        simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨environment, ⟨hEnvMem, hClock, hNoImmediate, hUnresolved⟩, rfl⟩
        have hEnvEq : environment = env := hPEnv
        subst environment
        have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = typeWaitingOffers env branches := hPCurrent.symm
        have hTargetEq : state' = TypeAutomatonState.root := by rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers (.offer alphabet elseType branches) \
            typeWaitingOffers env branches := by
          rw [← hPFuture, hRootFuture]
          rfl
        rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
            ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain,
              hBranchRelatedAgain⟩
        · simp only [Prod.mk.injEq] at hRootAgain
          have hResidualEq : residual' = .offer alphabet elseType branches := hRootAgain.1
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.offer_wait env alphabet elseType branches
            ⟨hWF, hClock, hNoImmediate, hUnresolved⟩,
            TypeOffers.offer_wait env alphabet elseType branches
              ⟨hWF, hClock, hNoImmediate, hUnresolved⟩⟩
        · exact absurd (by simpa [childState] using hStateEqAgain :
            (TypeAutomatonState.root : TypeAutomatonState) = .child 0 qAgain) (by simp)
        · exact absurd (by simpa [childState] using hStateEqAgain :
            (TypeAutomatonState.root : TypeAutomatonState) = .child (iAgain + 1) qAgain)
            (by simp)
      · -- else family: reconstructs `offer_else`
        simp only [Finset.mem_image, Finset.mem_filter] at hResolved2
        rcases hResolved2 with ⟨environment, ⟨hEnvMem, hClock, hNoImmediate, hResolvedNeeds⟩, rfl⟩
        have hEnvEq : environment = env := hPEnv
        subst environment
        have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = typeBranchActions branches := hPCurrent.symm
        have hTargetEq : state' = .child 0
            (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial := by
          rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers elseType := by
          rw [← hPFuture, Finset.sdiff_empty]
          exact hFutureElseEq ▸ rfl
        rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
            ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain,
              hBranchRelatedAgain⟩
        · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
        · have hQAgainEq : qAgain =
              (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial := by
            simpa [childState] using hStateEqAgain.symm
          rw [hQAgainEq] at hElseRelatedAgain
          have hResidualEq : residual' = elseType :=
            relationMembership_functional elseType (compileType signature elseType)
              hElseRelatedAgain (buildRelationSet_initial elseType
                (compileType signature elseType))
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.offer_else env alphabet elseType branches
            ⟨hWF, hClock, hNoImmediate, hResolvedNeeds⟩,
            TypeOffers.offer_else env alphabet elseType branches
              ⟨hWF, hClock, hNoImmediate, hResolvedNeeds⟩⟩
        · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
            iAgain + 1) (by omega)
  · -- else-child case: `hElseIH` reconstructs the step directly
    have hState' : state = .child 0 q := by simpa using hStateEq
    subst state
    have hElseSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈ (compileType signature elseType).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabetFor elseType.alphabet
      simpa [hElseAlphabet] using hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hElseIH hElseRelated hElseSymbol).mp hStep
      have hOuterEdge : (compileType signature (.offer alphabet elseType branches)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
          (.child 0 q) (.child 0 q') env label (TypeOfferSummary.mk current future)
          hSignatureSymbol]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature elseType q q'
          env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature elseType hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
            Finset.mem_union, childPendingEdges, Finset.mem_image]
          exact Or.inl (Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)))
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel elseType) elseType le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_selectedConjunctiveOffer_else signature elseType branches
                (.offer alphabet elseType branches) hWhole hElseFuelStrict hElseProductInfo
                t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      exact relationMembership_offer_else signature alphabet elseType branches
        hChildTargetRelated
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer alphabet elseType branches) (.child 0 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.offer alphabet elseType branches) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child 0 q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun selected' => (selected'.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
            (parallelTypeBranchesSelecting selected' branches))) q pendingEdge).mp
          ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature elseType).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature elseType q childEdge.target env
          label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hElseSymbol)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel elseType) elseType le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_selectedConjunctiveOffer_else signature elseType branches
                (.offer alphabet elseType branches) hWhole hElseFuelStrict hElseProductInfo
                t hStateMem]
      have hTargetEq : state' = .child 0 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
        ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain, hBranchRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · have hQAgainEq : qAgain = childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        rw [hQAgainEq] at hElseRelatedAgain
        exact (hElseIH hElseRelated hElseSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hElseRelatedAgain⟩
      · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
          iAgain + 1) (by omega)
  · -- branch-child case: the generated commit type's own correspondence (from
    -- the exclusive-offer/sequence/parallel cases) reconstructs the step directly
    have hState' : state = .child (i + 1) q := by simpa using hStateEq
    subst state
    have hSelectedMem : selected ∈ branches :=
      List.mem_iff_getElem?.mpr ⟨i, hSelectedEq⟩
    have hBranchIH : StepIffStatement signature
        (parallelTypeBranchesSelecting selected branches) :=
      correspondence_parallelTypeBranchesSelecting_stepIff signature alphabet
        branches hAlphaWF hAlphabetBranches hPairwise hSafe hBranchesIH selected
        hSelectedMem
    have hBranchSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈
        (compileType signature (parallelTypeBranchesSelecting selected branches)).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabetFor
          (parallelTypeBranchesSelecting selected branches).alphabet
      have hGeneratedAlphabet :
          (parallelTypeBranchesSelecting selected branches).alphabet = alphabet :=
        (parallelTypeBranchesSelecting_alphabet_wellFormed hAlphaWF hSelectedMem
          hAlphabetBranches hPairwise hSafe).1
      simpa [hGeneratedAlphabet] using hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hBranchIH hBranchRelated hBranchSymbol).mp hStep
      have hAutomataGet :
          (branches.map fun selected' => (selected'.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
            (parallelTypeBranchesSelecting selected' branches)))[i]? =
            some (selected.1, compileTypeFuel signature (typeCompilationFuel
              (parallelTypeBranchesSelecting selected branches))
              (parallelTypeBranchesSelecting selected branches)) := by
        rw [List.getElem?_map, hSelectedEq]
        rfl
      have hOuterEdge : (compileType signature (.offer alphabet elseType branches)).HasEdge
          (.child (i + 1) q) env label (TypeOfferSummary.mk current future)
          (.child (i + 1) q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
          (.child (i + 1) q) (.child (i + 1) q') env label
          (TypeOfferSummary.mk current future)
          hSignatureSymbol]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
          (parallelTypeBranchesSelecting selected branches)
          q q' env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature
            (parallelTypeBranchesSelecting selected branches) hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge (i + 1) childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
            Finset.mem_union]
          refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
          rw [indexedFragmentEdges, mem_foldl_union_iff]
          refine Or.inr ⟨(⟨selected.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches)⟩, i), ?_, ?_⟩
          · exact List.mk_mem_zipIdx_iff_getElem?.mpr hAutomataGet
          · simp only [childPendingEdges, Finset.mem_image]
            exact ⟨childEdge, hChildEdgeMem, rfl⟩
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
                (parallelTypeBranchesSelecting selected branches) le_rfl childEdge hChildEdgeMem
                t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
                (.offer alphabet elseType branches) hWhole i selected hSelectedEq
                (hBranchFuelStrict selected) (hBranchProductInfo i selected hSelectedEq)
                t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child (i + 1) q', hOuterEdge, ?_⟩
      exact relationMembership_offer_selected signature alphabet elseType branches
        hSelectedEq
        hChildTargetRelated
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hAutomataGet :
          (branches.map fun selected' => (selected'.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
            (parallelTypeBranchesSelecting selected' branches)))[i]? =
            some (selected.1, compileTypeFuel signature (typeCompilationFuel
              (parallelTypeBranchesSelecting selected branches))
              (parallelTypeBranchesSelecting selected branches)) := by
        rw [List.getElem?_map, hSelectedEq]
        rfl
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer alphabet elseType branches) (.child (i + 1) q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.offer alphabet elseType branches) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child (i + 1) q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildSelectedConjunctiveOfferAutomaton_outgoing_branch signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun selected' => (selected'.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
            (parallelTypeBranchesSelecting selected' branches)))
          i selected.1 (compileTypeFuel signature (typeCompilationFuel
            (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches))
          hAutomataGet q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature
          (parallelTypeBranchesSelecting selected branches)).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature
          (parallelTypeBranchesSelecting selected branches) q childEdge.target
          env label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hBranchSymbol)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
                (parallelTypeBranchesSelecting selected branches) le_rfl childEdge hChildEdgeMem
                t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
                (.offer alphabet elseType branches) hWhole i selected hSelectedEq
                (hBranchFuelStrict selected) (hBranchProductInfo i selected hSelectedEq)
                t hStateMem]
      have hTargetEq : state' = .child (i + 1) childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
        ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain, hBranchRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
          i + 1) (by omega)
      · have hSndEq : (TypeAutomatonState.child (iAgain + 1) qAgain) =
            .child (i + 1) childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        injection hSndEq with hIEq hQEq
        have hIAgainEq : iAgain = i := by omega
        subst hIAgainEq
        have hPairEq : selectedAgain = selected := by
          have h := hSelectedEqAgain.symm.trans hSelectedEq
          simpa using h
        rw [hPairEq, hQEq] at hBranchRelatedAgain
        exact (hBranchIH hBranchRelated hBranchSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hBranchRelatedAgain⟩

end

end Pact
