import Anvilpp.ProofHelpers.Regularity

namespace Pact

noncomputable section

open Classical

/-- Synchronized labels are tock together, so a non-clock product step has
non-clock component steps. -/
theorem typeLabel_sync_not_isTock (interface : Interface) (left right : TypeLabel)
    (hSync : TypeLabel.Sync interface left right)
    (hNotTock : ¬ (TypeLabel.combine interface left right).isTock) :
    ¬ left.isTock ∧ ¬ right.isTock := by
  cases left with
  | tock =>
      cases right with
      | tock => exact absurd (by simp [TypeLabel.combine, TypeLabel.isTock]) hNotTock
      | actions ra => exact absurd (hSync.2.2.mp trivial) (by simp [TypeLabel.isTock])
  | actions la =>
      cases right with
      | tock => exact absurd (hSync.2.2.mpr trivial) (by simp [TypeLabel.isTock])
      | actions ra => exact ⟨by simp [TypeLabel.isTock], by simp [TypeLabel.isTock]⟩

lemma helper_h12_compiled_state_shape
     {processType residual : PactType}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType processType))
        residual (compileType processType).initial) :
    (compileType processType).initial ∈
      (compileType processType).states :=
  compileType_initial_mem processType

/-- Helper Lemma H12, binary choice/offer-root case, shared by `.choice` and
`.fairChoice`. -/
theorem helper_h12_binaryChoice_shape
     (whole left right : PactType)
    (hUnfold :
      buildRelationSetCoreFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1) whole =
        insert (whole, TypeAutomatonState.root)
          ((buildRelationSetCoreFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left).image
              (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
            (buildRelationSetCoreFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) right).image
              (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))))
    (hFuelEq : typeCompilationFuel whole =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet whole (compileType whole))
        residual state) :
    (residual = whole ∧ state = TypeAutomatonState.root) ∨
    (∃ q1, state = .child 0 q1 ∧
      relationMembership (buildRelationSet left (compileType left)) residual q1) ∨
    (∃ q2, state = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType right)) residual q2) := by
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel
        (typeCompilationFuel whole) whole := hRelated
  rw [hFuelEq, hUnfold] at hMem
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hR, hS⟩ | ⟨entry, hEntry, hR, hS⟩ | ⟨entry, hEntry, hR, hS⟩
  · exact Or.inl ⟨hR, hS⟩
  · refine Or.inr (Or.inl ⟨entry.2, hS.symm, ?_⟩)
    show (residual, entry.2) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left
    rw [← buildRelationSetCoreFuel_eq_of_sufficient left (le_max_left _ _) le_rfl, ← hR]
    exact hEntry
  · refine Or.inr (Or.inr ⟨entry.2, hS.symm, ?_⟩)
    show (residual, entry.2) ∈ buildRelationSetCoreFuel (typeCompilationFuel right) right
    rw [← buildRelationSetCoreFuel_eq_of_sufficient right (le_max_right _ _) le_rfl, ← hR]
    exact hEntry

/-- Shape of a related pair for `.seq left right`: unlike choice/fairChoice
there is no fresh root (the sequence's own initial state IS `left`'s tagged
initial state, per `buildSequenceAutomaton`), so a state is tagged `.child 0`
with the residual still wrapped in `.seq _ right` (we haven't crossed over
yet) or tagged `.child 1` with the residual exactly `right`'s own (we have). -/
theorem helper_h12_seq_shape
     (alphabet : PactTypeAlphabet) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        residual state) :
    (∃ ρ q1, residual = .seq alphabet ρ right ∧ state = .child 0 q1 ∧
      relationMembership (buildRelationSet left (compileType left)) ρ q1 ∧
      (q1 ∉ (compileType left).accepting ∨
        q1 = (compileType left).initial)) ∨
    (∃ q2, state = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType right)) residual q2) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel] at hMem
  rcases Finset.mem_union.mp hMem with hLeft | hRight
  · rcases Finset.mem_image.mp hLeft with ⟨entry, hEntry, hEq⟩
    have hEntryMem := (Finset.mem_filter.mp hEntry).1
    have hSurvives := (Finset.mem_filter.mp hEntry).2
    injection hEq with hR hS
    refine Or.inl ⟨entry.1, entry.2, hR.symm, hS.symm, ?_, ?_⟩
    show (entry.1, entry.2) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left
    rw [← buildRelationSetCoreFuel_eq_of_sufficient left (le_max_left _ _) le_rfl]
    exact hEntryMem
    have hCompile := compileTypeFuel_eq_of_sufficient left
      (le_max_left (typeCompilationFuel left) (typeCompilationFuel right)) le_rfl
    rw [hCompile] at hSurvives
    change entry.2 ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting ∨
      entry.2 = (compileTypeFuel (typeCompilationFuel left) left).initial
    by_cases hAccepting :
        entry.2 ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting
    · exact Or.inr (by
        by_contra hNotInitial
        exact hSurvives (by simp [sequenceDeleted, hAccepting, hNotInitial]))
    · exact Or.inl hAccepting
  · rcases Finset.mem_image.mp hRight with ⟨entry, hEntry, hEq⟩
    injection hEq with hR hS
    refine Or.inr ⟨entry.2, hS.symm, ?_⟩
    show (residual, entry.2) ∈ buildRelationSetCoreFuel (typeCompilationFuel right) right
    rw [← buildRelationSetCoreFuel_eq_of_sufficient right (le_max_right _ _) le_rfl, ← hR]
    exact hEntry

private theorem stateProductInfoFuel_succ_stable :
    ∀ fuel processType state, typeCompilationFuel processType ≤ fuel →
      stateProductInfoFuel (fuel + 1) processType state =
        stateProductInfoFuel fuel processType state := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType state hFuel
      have := typeCompilationFuel_positive processType
      omega
  | succ fuel ih =>
      intro processType state hFuel
      cases processType with
      | skip _ => rfl
      | message _ _ _ => rfl
      | tock _ => rfl
      | progress _ _ => rfl
      | var _ _ => rfl
      | choice _ left right =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hLeft : typeCompilationFuel left ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) left q =
                    stateProductInfoFuel fuel left q
                  exact ih left q hLeft
              | succ i =>
                  cases i with
                  | zero =>
                      have hRight : typeCompilationFuel right ≤ fuel := by
                        simp [typeCompilationFuel] at hFuel; omega
                      change stateProductInfoFuel (fuel + 1) right q =
                        stateProductInfoFuel fuel right q
                      exact ih right q hRight
                  | succ i => rfl
          | _ => rfl
      | fairChoice _ bid left right =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hLeft : typeCompilationFuel left ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) left q =
                    stateProductInfoFuel fuel left q
                  exact ih left q hLeft
              | succ i =>
                  cases i with
                  | zero =>
                      have hRight : typeCompilationFuel right ≤ fuel := by
                        simp [typeCompilationFuel] at hFuel; omega
                      change stateProductInfoFuel (fuel + 1) right q =
                        stateProductInfoFuel fuel right q
                      exact ih right q hRight
                  | succ i => rfl
          | _ => rfl
      | seq _ left right =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hLeft : typeCompilationFuel left ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) left q =
                    stateProductInfoFuel fuel left q
                  exact ih left q hLeft
              | succ i =>
                  cases i with
                  | zero =>
                      have hRight : typeCompilationFuel right ≤ fuel := by
                        simp [typeCompilationFuel] at hFuel; omega
                      change stateProductInfoFuel (fuel + 1) right q =
                        stateProductInfoFuel fuel right q
                      exact ih right q hRight
                  | succ i => rfl
          | _ => rfl
      | par alphabet left right interface =>
          cases state with
          | pair q1 q2 => rfl
          | survivor i q =>
              cases i with
              | zero =>
                  have hLeft :
                      typeCompilationFuel (left.reannotate alphabet) ≤ fuel := by
                    rw [typeCompilationFuel_reannotate]
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1)
                      (left.reannotate alphabet) q =
                    stateProductInfoFuel fuel (left.reannotate alphabet) q
                  exact ih (left.reannotate alphabet) q hLeft
              | succ i =>
                  cases i with
                  | zero =>
                      have hRight :
                          typeCompilationFuel (right.reannotate alphabet) ≤
                            fuel := by
                        rw [typeCompilationFuel_reannotate]
                        simp [typeCompilationFuel] at hFuel; omega
                      change stateProductInfoFuel (fuel + 1)
                          (right.reannotate alphabet) q =
                        stateProductInfoFuel fuel (right.reannotate alphabet) q
                      exact ih (right.reannotate alphabet) q hRight
                  | succ i => rfl
          | _ => rfl
      | recur _ name body =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hBody : typeCompilationFuel body ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) body q =
                    stateProductInfoFuel fuel body q
                  exact ih body q hBody
              | succ i => rfl
          | _ => rfl
      | xoffer _ elseType branches =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hElse : typeCompilationFuel elseType ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) elseType q =
                    stateProductInfoFuel fuel elseType q
                  exact ih elseType q hElse
              | succ i =>
                  simp only [stateProductInfoFuel]
                  cases hGet : branches[i]? with
                  | none => simp
                  | some branch =>
                      simp only
                      have hMem : branch ∈ branches := List.mem_of_getElem? hGet
                      have hBranchFuel : typeCompilationFuel branch.2 ≤ fuel := by
                        have hBound :=
                          typeCompilationFuel_le_typeBranchCompilationFuel branches branch hMem
                        simp [typeCompilationFuel] at hFuel; omega
                      exact ih branch.2 q hBranchFuel
          | _ => rfl
      | offer alphabet elseType branches =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hElse : typeCompilationFuel elseType ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) elseType q =
                    stateProductInfoFuel fuel elseType q
                  exact ih elseType q hElse
              | succ i =>
                  simp only [stateProductInfoFuel]
                  cases hGet : branches[i]? with
                  | none => simp
                  | some selected =>
                      simp only
                      have hFuel' :
                          typeCompilationFuel (parallelTypeBranchesSelecting
                              alphabet selected branches) ≤ fuel := by
                        rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                        simp [typeCompilationFuel] at hFuel; omega
                      exact ih (parallelTypeBranchesSelecting alphabet selected branches) q hFuel'
          | _ => rfl

private theorem stateProductInfoFuel_add_stable
    (processType : PactType) (state : TypeAutomatonState)
    (fuel extra : Nat) (hFuel : typeCompilationFuel processType ≤ fuel) :
    stateProductInfoFuel (fuel + extra) processType state =
      stateProductInfoFuel fuel processType state := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        stateProductInfoFuel_succ_stable (fuel + extra) processType state (by omega), ih]

/-! ## Type-label ownership and synchronized recovery -/

set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-! ## Ownership of generated conjunctive-offer branch products -/

/-- Reannotation changes only fixed alphabets.  It preserves the structural
message, progress, and fair-choice footprints used by ownership. -/
theorem PactType.reannotate_ownership_data
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.MessageIds (processType.reannotate alphabet) =
        PactType.MessageIds processType ∧
      PactType.MessageActions (processType.reannotate alphabet) =
        PactType.MessageActions processType ∧
      PactType.ProgressIds (processType.reannotate alphabet) =
        PactType.ProgressIds processType ∧
      PactType.FairChoiceIds (processType.reannotate alphabet) =
        PactType.FairChoiceIds processType ∧
      (PactType.ParallelMessageOwnership (processType.reannotate alphabet) ↔
        PactType.ParallelMessageOwnership processType) ∧
      (PactType.ParallelProgressOwnership (processType.reannotate alphabet) ↔
        PactType.ParallelProgressOwnership processType) ∧
      (PactType.ParallelFairChoiceOwnership (processType.reannotate alphabet) ↔
        PactType.ParallelFairChoiceOwnership processType) := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType alphabet with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ branchAlphabet,
          PactType.BranchMessageIds
              (PactType.reannotateBranches branchAlphabet branches) =
              PactType.BranchMessageIds branches ∧
            PactType.BranchMessageActions
              (PactType.reannotateBranches branchAlphabet branches) =
              PactType.BranchMessageActions branches ∧
            PactType.BranchProgressIds
              (PactType.reannotateBranches branchAlphabet branches) =
              PactType.BranchProgressIds branches ∧
            PactType.BranchFairChoiceIds
              (PactType.reannotateBranches branchAlphabet branches) =
              PactType.BranchFairChoiceIds branches ∧
            (PactType.ParallelMessageOwnershipBranches
                (PactType.reannotateBranches branchAlphabet branches) ↔
              PactType.ParallelMessageOwnershipBranches branches) ∧
            (PactType.ParallelProgressOwnershipBranches
                (PactType.reannotateBranches branchAlphabet branches) ↔
              PactType.ParallelProgressOwnershipBranches branches) ∧
            (PactType.ParallelFairChoiceOwnershipBranches
                (PactType.reannotateBranches branchAlphabet branches) ↔
              PactType.ParallelFairChoiceOwnershipBranches branches) := by
        intro branches hBranchesSize branchAlphabet
        induction branches with
        | nil =>
            simp [PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
              PactType.ParallelMessageOwnershipBranches,
              PactType.ParallelProgressOwnershipBranches,
              PactType.ParallelFairChoiceOwnershipBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hType : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRest : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hTypeFacts :=
              ih (sizeOf branchType) hType branchAlphabet branchType rfl
            have hRestFacts := restIH hRest
            simp only [PactType.reannotateBranches_cons,
              PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
              PactType.ParallelMessageOwnershipBranches,
              PactType.ParallelProgressOwnershipBranches,
              PactType.ParallelFairChoiceOwnershipBranches]
            simp only [hTypeFacts.1, hTypeFacts.2.1, hTypeFacts.2.2.1,
              hTypeFacts.2.2.2.1, hTypeFacts.2.2.2.2.1,
              hTypeFacts.2.2.2.2.2.1, hTypeFacts.2.2.2.2.2.2,
              hRestFacts.1, hRestFacts.2.1, hRestFacts.2.2.1,
              hRestFacts.2.2.2.1, hRestFacts.2.2.2.2.1,
              hRestFacts.2.2.2.2.2.1, hRestFacts.2.2.2.2.2.2]
            simp
      have hOfferBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ branchAlphabet (seen : Finset BareMessage),
          PactType.BranchMessageIds
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
              PactType.BranchMessageIds branches ∧
            PactType.BranchMessageActions
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
              PactType.BranchMessageActions branches ∧
            PactType.BranchProgressIds
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
              PactType.BranchProgressIds branches ∧
            PactType.BranchFairChoiceIds
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
              PactType.BranchFairChoiceIds branches ∧
            (PactType.ParallelMessageOwnershipBranches
                (PactType.reannotateOfferBranches branchAlphabet seen
                  branches) ↔
              PactType.ParallelMessageOwnershipBranches branches) ∧
            (PactType.ParallelProgressOwnershipBranches
                (PactType.reannotateOfferBranches branchAlphabet seen
                  branches) ↔
              PactType.ParallelProgressOwnershipBranches branches) ∧
            (PactType.ParallelFairChoiceOwnershipBranches
                (PactType.reannotateOfferBranches branchAlphabet seen
                  branches) ↔
              PactType.ParallelFairChoiceOwnershipBranches branches) := by
        intro branches hBranchesSize branchAlphabet
        induction branches with
        | nil =>
            intro seen
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
              PactType.ParallelMessageOwnershipBranches,
              PactType.ParallelProgressOwnershipBranches,
              PactType.ParallelFairChoiceOwnershipBranches]
        | cons branch rest restIH =>
            intro seen
            rcases branch with ⟨action, branchType⟩
            have hType : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRest : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hTypeFacts := fun branchAlphabet' =>
              ih (sizeOf branchType) hType branchAlphabet' branchType rfl
            have hRestFacts := fun (seen' : Finset BareMessage) =>
              restIH hRest seen'
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
              PactType.ParallelMessageOwnershipBranches,
              PactType.ParallelProgressOwnershipBranches,
              PactType.ParallelFairChoiceOwnershipBranches]
            simp only [fun a => (hTypeFacts a).1, fun a => (hTypeFacts a).2.1,
              fun a => (hTypeFacts a).2.2.1,
              fun a => (hTypeFacts a).2.2.2.1,
              fun a => (hTypeFacts a).2.2.2.2.1,
              fun a => (hTypeFacts a).2.2.2.2.2.1,
              fun a => (hTypeFacts a).2.2.2.2.2.2,
              fun t => (hRestFacts t).1, fun t => (hRestFacts t).2.1,
              fun t => (hRestFacts t).2.2.1,
              fun t => (hRestFacts t).2.2.2.1,
              fun t => (hRestFacts t).2.2.2.2.1,
              fun t => (hRestFacts t).2.2.2.2.2.1,
              fun t => (hRestFacts t).2.2.2.2.2.2]
            simp
      have hBodies : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ branchAlphabet,
          (PactType.ParallelMessageOwnershipBodies
              (PactType.reannotateBranches branchAlphabet branches) ↔
            PactType.ParallelMessageOwnershipBodies branches) := by
        intro branches hBranchesSize branchAlphabet
        induction branches with
        | nil => simp [PactType.ParallelMessageOwnershipBodies]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hType : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRest : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            simp only [PactType.reannotateBranches_cons,
              PactType.ParallelMessageOwnershipBodies]
            rw [(ih (sizeOf branchType) hType branchAlphabet branchType
              rfl).2.2.2.2.1, restIH hRest]
      have hOfferBodies : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ branchAlphabet (seen : Finset BareMessage),
          (PactType.ParallelMessageOwnershipBodies
              (PactType.reannotateOfferBranches branchAlphabet seen branches) ↔
            PactType.ParallelMessageOwnershipBodies branches) := by
        intro branches hBranchesSize branchAlphabet
        induction branches with
        | nil =>
            intro seen
            simp [PactType.reannotateOfferBranches_nil,
              PactType.ParallelMessageOwnershipBodies]
        | cons branch rest restIH =>
            intro seen
            rcases branch with ⟨action, branchType⟩
            have hType : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRest : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.ParallelMessageOwnershipBodies]
            rw [(ih (sizeOf branchType) hType _ branchType
              rfl).2.2.2.2.1, restIH hRest _]
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership]
      | recur _ _ body =>
          have hBody : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simpa [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership] using
              ih (sizeOf body) hBody alphabet body rfl
      | choice _ left right | seq _ left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            ih (sizeOf left) hLeft alphabet left rfl,
            ih (sizeOf right) hRight alphabet right rfl]
      | fairChoice _ _ left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            ih (sizeOf left) hLeft alphabet left rfl,
            ih (sizeOf right) hRight alphabet right rfl]
      | par _ left right interface =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            ih (sizeOf left) hLeft
              (PactTypeAlphabet.projectParallel alphabet left.alphabet
                interface) left rfl,
            ih (sizeOf right) hRight
              (PactTypeAlphabet.projectParallel alphabet right.alphabet
                interface) right rfl]
      | xoffer _ elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            ih (sizeOf elseType) hElse alphabet elseType rfl,
            hBranches branches hBranchSize alphabet,
            hBodies branches hBranchSize alphabet]
      | offer _ elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            ih (sizeOf elseType) hElse alphabet elseType rfl,
            hOfferBranches branches hBranchSize alphabet ∅,
            hOfferBodies branches hBranchSize alphabet ∅]

@[simp] theorem PactType.messageIds_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.MessageIds (processType.reannotate alphabet) =
      PactType.MessageIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).1

@[simp] theorem PactType.messageActions_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.MessageActions (processType.reannotate alphabet) =
      PactType.MessageActions processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.1

@[simp] theorem PactType.progressIds_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.ProgressIds (processType.reannotate alphabet) =
      PactType.ProgressIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.1

@[simp] theorem PactType.fairChoiceIds_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.FairChoiceIds (processType.reannotate alphabet) =
      PactType.FairChoiceIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.2.1

/-- The generated branch-product worker preserves message names. -/
theorem parallelTypeBranchesWithin_messageIds
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType)) :
    PactType.MessageIds (parallelTypeBranchesWithin alphabet branches) =
      PactType.BranchMessageIds branches := by
  induction branches generalizing alphabet with
  | nil => simp [parallelTypeBranchesWithin, PactType.MessageIds,
      PactType.BranchMessageIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.MessageIds, PactType.BranchMessageIds]
      | cons next tail =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.MessageIds, PactType.BranchMessageIds, ih]

/-- The generated branch-product worker preserves polarized message actions. -/
theorem parallelTypeBranchesWithin_messageActions
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType)) :
    PactType.MessageActions (parallelTypeBranchesWithin alphabet branches) =
      PactType.BranchMessageActions branches := by
  induction branches generalizing alphabet with
  | nil => simp [parallelTypeBranchesWithin, PactType.MessageActions,
      PactType.BranchMessageActions]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.MessageActions, PactType.BranchMessageActions]
      | cons next tail =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.MessageActions, PactType.BranchMessageActions, ih]

/-- The generated branch-product worker preserves progress identifiers. -/
theorem parallelTypeBranchesWithin_progressIds
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType)) :
    PactType.ProgressIds (parallelTypeBranchesWithin alphabet branches) =
      PactType.BranchProgressIds branches := by
  induction branches generalizing alphabet with
  | nil => simp [parallelTypeBranchesWithin, PactType.ProgressIds,
      PactType.BranchProgressIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ProgressIds, PactType.BranchProgressIds]
      | cons next tail =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ProgressIds, PactType.BranchProgressIds, ih]

/-- The generated branch-product worker preserves fair-choice identifiers. -/
theorem parallelTypeBranchesWithin_fairChoiceIds
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType)) :
    PactType.FairChoiceIds (parallelTypeBranchesWithin alphabet branches) =
      PactType.BranchFairChoiceIds branches := by
  induction branches generalizing alphabet with
  | nil => simp [parallelTypeBranchesWithin, PactType.FairChoiceIds,
      PactType.BranchFairChoiceIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.FairChoiceIds, PactType.BranchFairChoiceIds]
      | cons next tail =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.FairChoiceIds, PactType.BranchFairChoiceIds, ih]

/-- Selecting a generated branch preserves the structural ownership data. -/
theorem parallelTypeBranchesSelectingWithin_ownershipData
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.MessageIds
        (parallelTypeBranchesSelectingWithin alphabet selected branches) =
        PactType.BranchMessageIds branches ∧
      PactType.MessageActions
        (parallelTypeBranchesSelectingWithin alphabet selected branches) =
        PactType.BranchMessageActions branches ∧
      PactType.ProgressIds
        (parallelTypeBranchesSelectingWithin alphabet selected branches) =
        PactType.BranchProgressIds branches ∧
      PactType.FairChoiceIds
        (parallelTypeBranchesSelectingWithin alphabet selected branches) =
        PactType.BranchFairChoiceIds branches := by
  induction branches generalizing alphabet with
  | nil =>
      simp [parallelTypeBranchesSelectingWithin, PactType.MessageIds,
        PactType.MessageActions, PactType.ProgressIds, PactType.FairChoiceIds,
        PactType.BranchMessageIds, PactType.BranchMessageActions,
        PactType.BranchProgressIds, PactType.BranchFairChoiceIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          by_cases hSelected : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelectingWithin,
              selectedTypeBranchAt, singletonTypeXOfferAt,
              PactType.MessageIds, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds]
          · simp [parallelTypeBranchesSelectingWithin, hSelected,
              selectedTypeBranchAt, singletonTypeXOfferAt,
              PactType.MessageIds, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds]
      | cons next tail =>
          by_cases hSelected : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelectingWithin,
              selectedTypeBranchAt, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.BranchMessageIds,
              PactType.BranchMessageActions, PactType.BranchProgressIds,
              PactType.BranchFairChoiceIds,
              parallelTypeBranchesWithin_messageIds,
              parallelTypeBranchesWithin_messageActions,
              parallelTypeBranchesWithin_progressIds,
              parallelTypeBranchesWithin_fairChoiceIds]
          · simp [parallelTypeBranchesSelectingWithin, hSelected,
              singletonTypeXOfferAt, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.BranchMessageIds,
              PactType.BranchMessageActions, PactType.BranchProgressIds,
              PactType.BranchFairChoiceIds, ih]

end

end Pact
