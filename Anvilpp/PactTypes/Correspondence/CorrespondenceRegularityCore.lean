import Anvilpp.PactTypes.Correspondence.CorrespondenceSequenceAssembly

/-!
# Regularity transport: skipping/completing, tail-occurrence, binder, variable-edge invariants
-/

namespace Pact

noncomputable section

/-- Literal termination is always a same-cycle completion.  This is a
compiler invariant, not a semantic assumption: every constructor transports
child `skipping` states into its `completing` metadata, and recursion includes
the body's completing states in the seed of its non-clock predecessor
closure. -/
private theorem compileTypeFuel_skipping_subset_completing
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
        (compileTypeFuel signature fuel processType).skipping ⊆
          (compileTypeFuel signature fuel processType).completing := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel state hSkipping
      cases processType with
      | message msg dir =>
          simpa [compileTypeFuel, finishAutomatonFragment] using
            (Or.inr hSkipping)
      | progress pid =>
          simpa [compileTypeFuel, finishAutomatonFragment] using
            (Or.inr hSkipping)
      | tock =>
          simpa [compileTypeFuel, finishAutomatonFragment] using hSkipping
      | skip =>
          simpa [compileTypeFuel, finishAutomatonFragment] using hSkipping
      | var name =>
          simp [compileTypeFuel, finishAutomatonFragment] at hSkipping
      | recur name body =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hBody := ih body hBodyFuel
          let bodyFragment := compileTypeFuel signature fuel body
          have hCompletion := buildRecursionAutomaton_completing_eq signature
            name bodyFragment
          simp only [compileTypeFuel] at hSkipping ⊢
          rw [hCompletion]
          have hChild : ∃ child ∈ bodyFragment.skipping,
              childState 0 child = state := by
            simpa [bodyFragment, buildRecursionAutomaton,
              finishAutomatonFragment, childSkipping] using hSkipping
          rcases hChild with ⟨child, hChildSkipping, rfl⟩
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨child, completingBackClosure_superset_seed bodyFragment _ ?_,
            rfl⟩
          exact Finset.mem_union_right _ (hBody hChildSkipping)
      | choice left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hLeft := ih left hLeftFuel
          have hRight := ih right hRightFuel
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hSkipping ⊢
          rcases hSkipping with hLeftSkipping | hRightSkipping
          · simp only [childSkipping, Finset.mem_image] at hLeftSkipping
            rcases hLeftSkipping with ⟨child, hChild, rfl⟩
            exact Or.inl (Or.inr (by
              simp only [childCompleting, Finset.mem_image]
              exact ⟨child, hLeft hChild, rfl⟩))
          · simp only [childSkipping, Finset.mem_image] at hRightSkipping
            rcases hRightSkipping with ⟨child, hChild, rfl⟩
            exact Or.inr (by
              simp only [childCompleting, Finset.mem_image]
              exact ⟨child, hRight hChild, rfl⟩)
      | fairChoice bid left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hLeft := ih left hLeftFuel
          have hRight := ih right hRightFuel
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hSkipping ⊢
          rcases hSkipping with hLeftSkipping | hRightSkipping
          · simp only [childSkipping, Finset.mem_image] at hLeftSkipping
            rcases hLeftSkipping with ⟨child, hChild, rfl⟩
            exact Or.inl (Or.inr (by
              simp only [childCompleting, Finset.mem_image]
              exact ⟨child, hLeft hChild, rfl⟩))
          · simp only [childSkipping, Finset.mem_image] at hRightSkipping
            rcases hRightSkipping with ⟨child, hChild, rfl⟩
            exact Or.inr (by
              simp only [childCompleting, Finset.mem_image]
              exact ⟨child, hRight hChild, rfl⟩)
      | seq left right =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight := ih right hRightFuel
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hSkipping ⊢
          simp only [childSkipping, Finset.mem_image] at hSkipping
          rcases hSkipping with ⟨child, hChild, rfl⟩
          exact Or.inr (by
            simp only [childCompleting, Finset.mem_image]
            exact ⟨child, hRight hChild, rfl⟩)
      | par left right interface =>
          simp [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment] at hSkipping
      | xoffer elseType branches =>
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hBranchFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          let automata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          have hElse := ih elseType hElseFuel
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hSkipping ⊢
          rcases hSkipping with hElseSkipping | hIndexedSkipping
          · simp only [childSkipping, Finset.mem_image] at hElseSkipping
            rcases hElseSkipping with ⟨child, hChild, rfl⟩
            exact Or.inl (Or.inr (by
              simp only [childCompleting, Finset.mem_image]
              exact ⟨child, hElse hChild, rfl⟩))
          ·
            rw [indexedFragmentSkipping, mem_foldl_union_iff] at hIndexedSkipping
            rw [indexedFragmentCompleting, mem_foldl_union_iff]
            rcases hIndexedSkipping with hEmpty | ⟨indexed, hIndexed, hChild⟩
            · simp at hEmpty
            · right
              right
              refine ⟨indexed, hIndexed, ?_⟩
              simp only [automata, childSkipping, Finset.mem_image] at hChild
              rcases hChild with ⟨child, hChildSkipping, rfl⟩
              simp only [childCompleting, Finset.mem_image]
              refine ⟨child, ?_, rfl⟩
              have hEntryMem : indexed.1 ∈ branches.map fun branch =>
                  (branch.1, compileTypeFuel signature fuel branch.2) := by
                have hMapped := List.mem_map_of_mem (f := Prod.fst) hIndexed
                simpa using hMapped
              rcases List.mem_map.mp hEntryMem with
                ⟨branch, hBranch, hEntry⟩
              have hFragment : indexed.1.2 =
                  compileTypeFuel signature fuel branch.2 := by
                exact (congrArg Prod.snd hEntry).symm
              rw [hFragment] at hChildSkipping ⊢
              exact ih branch.2
                (le_trans
                  (typeCompilationFuel_le_typeBranchCompilationFuel branches
                    branch hBranch) hBranchFuel) hChildSkipping
      | offer elseType branches =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hConjunctionFuel : conjunctiveCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          let automata := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          have hElse := ih elseType hElseFuel
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hSkipping ⊢
          rcases hSkipping with hElseSkipping | hIndexedSkipping
          · simp only [childSkipping, Finset.mem_image] at hElseSkipping
            rcases hElseSkipping with ⟨child, hChild, rfl⟩
            exact Or.inl (Or.inr (by
              simp only [childCompleting, Finset.mem_image]
              exact ⟨child, hElse hChild, rfl⟩))
          ·
            rw [indexedFragmentSkipping, mem_foldl_union_iff] at hIndexedSkipping
            rw [indexedFragmentCompleting, mem_foldl_union_iff]
            rcases hIndexedSkipping with hEmpty | ⟨indexed, hIndexed, hChild⟩
            · simp at hEmpty
            · right
              right
              refine ⟨indexed, hIndexed, ?_⟩
              simp only [automata, childSkipping, Finset.mem_image] at hChild
              rcases hChild with ⟨child, hChildSkipping, rfl⟩
              simp only [childCompleting, Finset.mem_image]
              refine ⟨child, ?_, rfl⟩
              have hEntryMem : indexed.1 ∈ branches.map fun selected =>
                  (selected.1, compileTypeFuel signature fuel
                    (parallelTypeBranchesSelecting selected branches)) := by
                have hMapped := List.mem_map_of_mem (f := Prod.fst) hIndexed
                simpa using hMapped
              rcases List.mem_map.mp hEntryMem with
                ⟨selected, hSelected, hEntry⟩
              have hFragment : indexed.1.2 = compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting selected branches) := by
                exact (congrArg Prod.snd hEntry).symm
              rw [hFragment] at hChildSkipping ⊢
              apply ih (parallelTypeBranchesSelecting selected branches)
                _ hChildSkipping
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranchesSelecting]
              exact hConjunctionFuel

/-- Every element of a branch list inherits the ambient tail flag. -/
theorem tailBranchOccurrences_mem
    (name : String) (tail : Prop) :
    ∀ (branches : List (BareMessage × PactType))
      (entry : BareMessage × PactType),
      PactType.TailBranchOccurrences name tail branches →
      entry ∈ branches →
        PactType.TailOccurrences name tail entry.2 := by
  intro branches
  induction branches with
  | nil => intro entry _ hMem; simp at hMem
  | cons head rest ih =>
      intro entry hTail hMem
      obtain ⟨action, processType⟩ := head
      simp only [PactType.TailBranchOccurrences] at hTail
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact hTail.1
      · exact ih entry hTail.2 hRest

private theorem tailOccurrences_parallelTypeBranches
    (name : String) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.TailBranchOccurrences name False branches →
        PactType.TailOccurrences name False
          (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil => intro _; simp [parallelTypeBranches, PactType.TailOccurrences]
  | cons branch rest ih =>
      obtain ⟨action, processType⟩ := branch
      intro hTail
      have hFields : PactType.TailOccurrences name False processType ∧
          PactType.TailBranchOccurrences name False rest := by
        simpa only [PactType.TailBranchOccurrences] using hTail
      cases rest with
      | nil =>
          simp only [parallelTypeBranches, singletonTypeXOffer,
            PactType.TailOccurrences, PactType.TailBranchOccurrences]
          exact ⟨trivial, hFields.1, trivial⟩
      | cons next tailBranches =>
          simp only [parallelTypeBranches, singletonTypeXOffer,
            PactType.TailOccurrences, PactType.TailBranchOccurrences]
          exact ⟨⟨trivial, hFields.1, trivial⟩, ih hFields.2⟩

theorem tailOccurrences_parallelTypeBranchesSelecting
    (name : String) (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.TailBranchOccurrences name False branches →
        PactType.TailOccurrences name False
          (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _
      simp [parallelTypeBranchesSelecting, PactType.TailOccurrences]
  | cons branch rest ih =>
      obtain ⟨action, processType⟩ := branch
      intro hTail
      have hFields : PactType.TailOccurrences name False processType ∧
          PactType.TailBranchOccurrences name False rest := by
        simpa only [PactType.TailBranchOccurrences] using hTail
      cases rest with
      | nil =>
          by_cases hSelected : (action, processType) = selected
          · simp only [parallelTypeBranchesSelecting, if_pos hSelected,
              selectedTypeBranch, PactType.TailOccurrences]
            exact ⟨trivial, hFields.1⟩
          · simp only [parallelTypeBranchesSelecting, if_neg hSelected,
              singletonTypeXOffer, PactType.TailOccurrences,
              PactType.TailBranchOccurrences]
            exact ⟨trivial, hFields.1, trivial⟩
      | cons next tailBranches =>
          by_cases hSelected : (action, processType) = selected
          · simp only [parallelTypeBranchesSelecting, if_pos hSelected,
              selectedTypeBranch, PactType.TailOccurrences]
            exact ⟨⟨trivial, hFields.1⟩,
              tailOccurrences_parallelTypeBranches name _ hFields.2⟩
          · simp only [parallelTypeBranchesSelecting, if_neg hSelected,
              singletonTypeXOffer, PactType.TailOccurrences,
              PactType.TailBranchOccurrences]
            exact ⟨⟨trivial, hFields.1, trivial⟩, ih hFields.2⟩

private theorem tailRecursive_parallelTypeBranches :
    ∀ branches : List (BareMessage × PactType),
      PactType.TailRecursiveBranches branches →
        PactType.TailRecursive (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil => simp [parallelTypeBranches, PactType.TailRecursive]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hTail
      have hFields : branchType.TailRecursive ∧
          PactType.TailRecursiveBranches rest := by
        simpa only [PactType.TailRecursiveBranches] using hTail
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.TailRecursive, PactType.TailRecursiveBranches] using
              hFields.1
      | cons next tail =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.TailRecursive, PactType.TailRecursiveBranches] using
              And.intro hFields.1 (ih hFields.2)

theorem tailRecursive_parallelTypeBranchesSelecting
    (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      PactType.TailRecursiveBranches branches →
        PactType.TailRecursive
          (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.TailRecursive]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hTail
      have hFields : branchType.TailRecursive ∧
          PactType.TailRecursiveBranches rest := by
        simpa only [PactType.TailRecursiveBranches] using hTail
      cases rest with
      | nil =>
          by_cases hSelected : (action, branchType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.TailRecursive, hFields.1]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.TailRecursive,
              PactType.TailRecursiveBranches, hFields.1]
      | cons next tail =>
          by_cases hSelected : (action, branchType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.TailRecursive, hFields.1,
              tailRecursive_parallelTypeBranches (next :: tail) hFields.2]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.TailRecursive,
              PactType.TailRecursiveBranches, hFields.1, ih hFields.2]

private theorem binderHygienic_parallelTypeBranches (bound : List String) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BinderHygienicBranches bound branches →
        PactType.BinderHygienic bound (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil => simp [parallelTypeBranches, PactType.BinderHygienic]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hHygienic
      have hFields : branchType.BinderHygienic bound ∧
          PactType.BinderHygienicBranches bound rest := by
        simpa only [PactType.BinderHygienicBranches] using hHygienic
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.BinderHygienic, PactType.BinderHygienicBranches] using
              hFields.1
      | cons next tail =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.BinderHygienic, PactType.BinderHygienicBranches] using
              And.intro hFields.1 (ih hFields.2)

theorem binderHygienic_parallelTypeBranchesSelecting
    (bound : List String) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BinderHygienicBranches bound branches →
        PactType.BinderHygienic bound
          (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.BinderHygienic]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hHygienic
      have hFields : branchType.BinderHygienic bound ∧
          PactType.BinderHygienicBranches bound rest := by
        simpa only [PactType.BinderHygienicBranches] using hHygienic
      cases rest with
      | nil =>
          by_cases hSelected : (action, branchType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.BinderHygienic, hFields.1]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.BinderHygienic,
              PactType.BinderHygienicBranches, hFields.1]
      | cons next tail =>
          by_cases hSelected : (action, branchType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.BinderHygienic, hFields.1,
              binderHygienic_parallelTypeBranches bound (next :: tail)
                hFields.2]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.BinderHygienic,
              PactType.BinderHygienicBranches, hFields.1, ih hFields.2]

/- Binder-context preservation for represented residuals. -/
private theorem compilationRelation_allVariablesBound
    {bound : List String} {original residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : TypeCompilationRelation original state residual) :
    original.AllVariablesBound bound → residual.AllVariablesBound bound := by
  intro hBound
  induction hRelated generalizing bound with
  | skip => simpa [PactType.AllVariablesBound]
  | message_source => simpa
  | message_final => simp [PactType.AllVariablesBound]
  | cycle_source => simpa
  | cycle_final => simp [PactType.AllVariablesBound]
  | progress_source => simpa
  | progress_final => simp [PactType.AllVariablesBound]
  | «variable» => simpa
  | recur_source => simpa
  | recur_body name body childResidual childState hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      apply PactType.replaceVar_allVariablesBound bound name (.recur name body)
      · simpa [PactType.AllVariablesBound] using hBound
      · exact ih (bound := name :: bound) hBound
  | choice_source => simpa
  | choice_left left right childResidual childState hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      exact ih hBound.1
  | choice_right left right childResidual childState hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      exact ih hBound.2
  | fair_source => simpa
  | fair_left bid left right childResidual childState hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      exact ih hBound.1
  | fair_right bid left right childResidual childState hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      exact ih hBound.2
  | sequence_left left right childResidual childState hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound ⊢
      exact ⟨ih hBound.1, hBound.2⟩
  | sequence_right left right childResidual childState hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      exact ih hBound.2
  | parallel left right leftResidual rightResidual interface leftState
      rightState hLeft hRight ihLeft ihRight =>
      simp only [PactType.AllVariablesBound] at hBound ⊢
      exact ⟨ihLeft hBound.1, ihRight hBound.2⟩
  | xoffer_source => simpa
  | xoffer_else elseType childResidual branches childState hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      exact ih hBound.1
  | xoffer_branch elseType branchType childResidual branches action index
      childState hEntry hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      have hMember : (action, branchType) ∈ branches :=
        List.mem_of_getElem? hEntry
      exact ih (allVariablesBound_branch_of_mem bound branches
        (action, branchType) hBound.2 hMember)
  | offer_source => simpa
  | offer_branches elseType childResidual branches selected index childState
      hEntry hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      exact ih (allVariablesBound_parallelTypeBranchesSelecting bound selected
        branches hBound.2)
  | offer_else elseType childResidual branches childState hChild ih =>
      simp only [PactType.AllVariablesBound] at hBound
      exact ih hBound.1

/- A represented residual may cease to be hygienic after unfolding (the
replacement can carry binders below a sibling binder), but it remains fresh
for every externally active binder name.  This is exactly what substitution
fusion needs. -/
theorem compilationRelation_binderFreshFor
    {forbidden : List String} {original residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : TypeCompilationRelation original state residual) :
    original.BinderHygienic forbidden → residual.BinderFreshFor forbidden := by
  intro hHygienic
  induction hRelated generalizing forbidden with
  | skip => simp [PactType.BinderFreshFor]
  | message_source => simp [PactType.BinderFreshFor]
  | message_final => simp [PactType.BinderFreshFor]
  | cycle_source => simp [PactType.BinderFreshFor]
  | cycle_final => simp [PactType.BinderFreshFor]
  | progress_source => simp [PactType.BinderFreshFor]
  | progress_final => simp [PactType.BinderFreshFor]
  | «variable» => simp [PactType.BinderFreshFor]
  | recur_source => exact PactType.binderHygienic_binderFreshFor _ _ hHygienic
  | recur_body name body childResidual childState hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      have hReplacementFresh :
          (PactType.recur name body).BinderFreshFor forbidden := by
        simp only [PactType.BinderFreshFor]
        exact ⟨hHygienic.1,
          PactType.binderHygienic_binderFreshFor forbidden body
            (PactType.binderHygienic_mono
              (by intro x hx; exact List.mem_cons_of_mem name hx)
              body hHygienic.2)⟩
      apply PactType.replaceVar_binderFreshFor forbidden name (.recur name body)
        hReplacementFresh childResidual
      exact ih (forbidden := name :: forbidden) hHygienic.2
  | choice_source => exact PactType.binderHygienic_binderFreshFor _ _ hHygienic
  | choice_left left right childResidual childState hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      exact ih hHygienic.1
  | choice_right left right childResidual childState hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      exact ih hHygienic.2
  | fair_source => exact PactType.binderHygienic_binderFreshFor _ _ hHygienic
  | fair_left bid left right childResidual childState hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      exact ih hHygienic.1
  | fair_right bid left right childResidual childState hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      exact ih hHygienic.2
  | sequence_left left right childResidual childState hChild ih =>
      simp only [PactType.BinderHygienic, PactType.BinderFreshFor]
        at hHygienic ⊢
      exact ⟨ih hHygienic.1,
        PactType.binderHygienic_binderFreshFor forbidden right hHygienic.2⟩
  | sequence_right left right childResidual childState hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      exact ih hHygienic.2
  | parallel left right leftResidual rightResidual interface leftState
      rightState hLeft hRight ihLeft ihRight =>
      simp only [PactType.BinderHygienic, PactType.BinderFreshFor]
        at hHygienic ⊢
      exact ⟨ihLeft hHygienic.1, ihRight hHygienic.2⟩
  | xoffer_source => exact PactType.binderHygienic_binderFreshFor _ _ hHygienic
  | xoffer_else elseType childResidual branches childState hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      exact ih hHygienic.1
  | xoffer_branch elseType branchType childResidual branches action index
      childState hEntry hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      have hMember : (action, branchType) ∈ branches :=
        List.mem_of_getElem? hEntry
      exact ih (binderHygienic_branch_of_mem forbidden branches
        (action, branchType) hHygienic.2 hMember)
  | offer_source => exact PactType.binderHygienic_binderFreshFor _ _ hHygienic
  | offer_branches elseType childResidual branches selected index childState
      hEntry hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      exact ih (binderHygienic_parallelTypeBranchesSelecting forbidden selected
        branches hHygienic.2)
  | offer_else elseType childResidual branches childState hChild ih =>
      simp only [PactType.BinderHygienic] at hHygienic
      exact ih hHygienic.1

/- A forbidden tail occurrence remains forbidden in every residual represented
by a compiler state.  The recursion case is the only non-structural one:
same-name replacement removes the free name, while a different binder uses
the general substitution-preservation theorem. -/
theorem compilationRelation_tailOccurrences_false
    (name : String) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : TypeCompilationRelation processType state residual) :
    processType.TailOccurrences name False →
      residual.TailOccurrences name False := by
  induction hRelated with
  | skip => simp [PactType.TailOccurrences]
  | message_source msg dir => intro hTail; exact hTail
  | message_final msg dir => simp [PactType.TailOccurrences]
  | cycle_source => intro hTail; exact hTail
  | cycle_final => simp [PactType.TailOccurrences]
  | progress_source pid => intro hTail; exact hTail
  | progress_final pid => simp [PactType.TailOccurrences]
  | «variable» other => intro hTail; exact hTail
  | recur_source binder body => intro hTail; exact hTail
  | recur_body binder body childResidual childState hChild ih =>
      intro hTail
      by_cases hName : binder = name
      · subst binder
        exact PactType.tailOccurrences_false_replaceVar_self_recur name body
          childResidual
      · have hBodyTail : body.TailOccurrences name False := by
          simpa only [PactType.TailOccurrences, if_neg hName] using hTail
        exact PactType.tailOccurrences_false_replaceVar name binder
          (.recur binder body) hTail childResidual (ih hBodyTail)
  | choice_source left right => intro hTail; exact hTail
  | choice_left left right childResidual childState hChild ih =>
      intro hTail
      have hFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih hFields.1
  | choice_right left right childResidual childState hChild ih =>
      intro hTail
      have hFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih hFields.2
  | fair_source bid left right => intro hTail; exact hTail
  | fair_left bid left right childResidual childState hChild ih =>
      intro hTail
      have hFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih hFields.1
  | fair_right bid left right childResidual childState hChild ih =>
      intro hTail
      have hFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih hFields.2
  | sequence_left left right childResidual childState hChild ih =>
      intro hTail
      have hFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      simpa only [PactType.TailOccurrences] using And.intro
        (ih hFields.1) hFields.2
  | sequence_right left right childResidual childState hChild ih =>
      intro hTail
      have hFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih hFields.2
  | parallel left right leftResidual rightResidual interface leftState
      rightState hLeft hRight ihLeft ihRight =>
      intro hTail
      have hFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      simpa only [PactType.TailOccurrences] using And.intro
        (ihLeft hFields.1) (ihRight hFields.2)
  | xoffer_source elseType branches => intro hTail; exact hTail
  | xoffer_else elseType childResidual branches childState hChild ih =>
      intro hTail
      have hFields : elseType.TailOccurrences name False ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih hFields.1
  | xoffer_branch elseType branchType childResidual branches action index
      childState hEntry hChild ih =>
      intro hTail
      have hFields : elseType.TailOccurrences name False ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih (tailBranchOccurrences_mem name False branches
        (action, branchType) hFields.2 (List.mem_of_getElem? hEntry))
  | offer_source elseType branches => intro hTail; exact hTail
  | offer_branches elseType childResidual branches selected index childState
      hEntry hChild ih =>
      intro hTail
      have hFields : elseType.TailOccurrences name False ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih (tailOccurrences_parallelTypeBranchesSelecting name selected
        branches hFields.2)
  | offer_else elseType childResidual branches childState hChild ih =>
      intro hTail
      have hFields : elseType.TailOccurrences name False ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih hFields.1

/- In a represented non-tail context, parametric recursion completion is
literally ordinary syntax completion. -/
private theorem compilationRelation_canCompleteBeforeTockSubst_eq_of_false
    (name : String) (value : Bool) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : TypeCompilationRelation processType state residual)
    (hTail : processType.TailOccurrences name False) :
    PactType.canCompleteBeforeTockSubst name value residual =
      residual.CanCompleteBeforeTock :=
  PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false name value
    residual (compilationRelation_tailOccurrences_false name hRelated hTail)

/-- **Recursive-call sources represent bare variables.**

If a compiled fragment still carries an unresolved `.variable name` marker
edge, then — provided `name` occurs only in tail position — the source of that
edge represents exactly the residual `PactType.var name`, and the ambient tail
flag holds.

The `tail` conjunct is what makes the induction go through: a `.variable name`
marker occurring in a non-tail position (the left of a sequence, either side
of a parallel composition, or a conjunctive-offer branch) is impossible,
because there `TailOccurrences name False` holds and the conclusion `tail`
degenerates to `False`.  In the tail positions that remain (choice branches,
the right of a sequence, exclusive-offer continuations, and the body of a
non-shadowing binder) the representative residual is transported unchanged by
the corresponding `TypeCompilationRelation` constructor, so it stays
`PactType.var name`; under a non-shadowing binder `replaceVar` leaves it
alone, which is why `other ≠ name` is extracted first.

Stating the conclusion as the relation itself (rather than as uniqueness of
the represented residual) additionally supplies *existence* of a
representative, which the seed-inclusion step of
`recursionBodyCompletingClosure_subset` needs.

The induction mirrors `compileTypeFuel_futureTargetsInStates`: structural on
the compilation fuel, one case per constructor of the compiler. -/
theorem compileTypeFuel_variableEdge_source_var
    (signature : TypeAlphabet) (name : String) :
    ∀ (fuel : Nat) (processType : PactType) (tail : Prop),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailOccurrences name tail processType →
      ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
        edge.label = AutomatonConstructionLabel.variable name →
          tail ∧ TypeCompilationRelation processType edge.source
            (PactType.var name) := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType tail hFuel
      exact (Nat.not_lt_zero _ (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType tail hFuel hTail edge hEdge hLabel
      cases processType with
      | skip =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩
          rw [← hEq] at hLabel
          exact absurd hLabel (by simp)
      | message msg dir =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ((⟨e, _, hEq⟩ | ⟨e, _, hEq⟩) | ⟨e, _, hEq⟩) <;>
            (rw [← hEq] at hLabel; exact absurd hLabel (by simp))
      | tock =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨e, _, hEq⟩ | ⟨e, _, hEq⟩)
          · rw [← hEq] at hLabel
            split at hLabel <;> exact absurd hLabel (by simp)
          · rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
      | progress pid =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨e, _, hEq⟩ | ⟨e, _, hEq⟩) <;>
            (rw [← hEq] at hLabel; exact absurd hLabel (by simp))
      | var other =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩
          rw [← hEq] at hLabel
          have hName : other = name := by
            simpa using hLabel
          subst hName
          have hSource : edge.source = TypeAutomatonState.root := by
            rw [← hEq]
          refine ⟨?_, ?_⟩
          · simpa [PactType.TailOccurrences] using hTail
          · rw [hSource]
            exact TypeCompilationRelation.variable _
      | recur other body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
            at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩ | ⟨bodyEdge, hBodyEdge, hEq⟩
          · exfalso
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
          · by_cases hVarOther :
                bodyEdge.label = AutomatonConstructionLabel.variable other
            · exfalso
              rw [if_pos hVarOther] at hEq
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
            · rw [if_neg hVarOther] at hEq
              have hBodyLabel :
                  bodyEdge.label = AutomatonConstructionLabel.variable name := by
                rw [← hEq] at hLabel
                exact hLabel
              have hOther : other ≠ name := by
                intro hEqName
                exact hVarOther (hEqName ▸ hBodyLabel)
              have hTailBody : PactType.TailOccurrences name tail body := by
                have hTail' := hTail
                simp only [PactType.TailOccurrences] at hTail'
                rw [if_neg hOther] at hTail'
                exact hTail'
              have hIH := ih body tail hBody hTailBody bodyEdge hBodyEdge
                hBodyLabel
              refine ⟨hIH.1, ?_⟩
              have hSource :
                  edge.source = TypeAutomatonState.child 0 bodyEdge.source := by
                rw [← hEq]; rfl
              rw [hSource]
              have hRecur := TypeCompilationRelation.recur_body other body
                (PactType.var name) bodyEdge.source hIH.2
              simpa [PactType.replaceVar, hOther] using hRecur
      | choice left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hTailLeft : PactType.TailOccurrences name tail left ∧
              PactType.TailOccurrences name tail right := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton] at hEdge
          rcases hEdge with (⟨childEdge, hChildEdge, hEq⟩ |
            ⟨childEdge, hChildEdge, hEq⟩) | ⟨environment, _, hEq | hEq⟩
          · have hChildLabel :
                childEdge.label = AutomatonConstructionLabel.variable name := by
              rw [← hEq] at hLabel
              exact hLabel
            have hIH := ih left tail hLeft hTailLeft.1 childEdge hChildEdge
              hChildLabel
            refine ⟨hIH.1, ?_⟩
            have hSource : edge.source =
                TypeAutomatonState.child 0 childEdge.source := by
              rw [← hEq]; rfl
            rw [hSource]
            exact TypeCompilationRelation.choice_left left right
              (PactType.var name) childEdge.source hIH.2
          · have hChildLabel :
                childEdge.label = AutomatonConstructionLabel.variable name := by
              rw [← hEq] at hLabel
              exact hLabel
            have hIH := ih right tail hRight hTailLeft.2 childEdge hChildEdge
              hChildLabel
            refine ⟨hIH.1, ?_⟩
            have hSource : edge.source =
                TypeAutomatonState.child 1 childEdge.source := by
              rw [← hEq]; rfl
            rw [hSource]
            exact TypeCompilationRelation.choice_right left right
              (PactType.var name) childEdge.source hIH.2
          · exfalso
            rw [hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            rw [hEq] at hLabel
            exact absurd hLabel (by simp)
      | fairChoice bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hTailLeft : PactType.TailOccurrences name tail left ∧
              PactType.TailOccurrences name tail right := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton] at hEdge
          rcases hEdge with (⟨childEdge, hChildEdge, hEq⟩ |
            ⟨childEdge, hChildEdge, hEq⟩) | ⟨environment, _, hEq | hEq⟩
          · have hChildLabel :
                childEdge.label = AutomatonConstructionLabel.variable name := by
              rw [← hEq] at hLabel
              exact hLabel
            have hIH := ih left tail hLeft hTailLeft.1 childEdge hChildEdge
              hChildLabel
            refine ⟨hIH.1, ?_⟩
            have hSource : edge.source =
                TypeAutomatonState.child 0 childEdge.source := by
              rw [← hEq]; rfl
            rw [hSource]
            exact TypeCompilationRelation.fair_left bid left right
              (PactType.var name) childEdge.source hIH.2
          · have hChildLabel :
                childEdge.label = AutomatonConstructionLabel.variable name := by
              rw [← hEq] at hLabel
              exact hLabel
            have hIH := ih right tail hRight hTailLeft.2 childEdge hChildEdge
              hChildLabel
            refine ⟨hIH.1, ?_⟩
            have hSource : edge.source =
                TypeAutomatonState.child 1 childEdge.source := by
              rw [← hEq]; rfl
            rw [hSource]
            exact TypeCompilationRelation.fair_right bid left right
              (PactType.var name) childEdge.source hIH.2
          · exfalso
            rw [hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            rw [hEq] at hLabel
            exact absurd hLabel (by simp)
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences name False left ∧
              PactType.TailOccurrences name tail right := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion] at hEdge
          rcases hEdge with ((⟨childEdge, hChildEdge, hEq⟩ |
              ⟨childEdge, hChildEdge, hEq⟩) |
            ⟨skipState, _, environment, _, hEq⟩) | ⟨completeState, _, hEq⟩
          · exact absurd (ih left False hLeft hTailFields.1 childEdge
              hChildEdge (by rw [← hEq] at hLabel; exact hLabel)).1 (by simp)
          · have hChildLabel :
                childEdge.label = AutomatonConstructionLabel.variable name := by
              rw [← hEq] at hLabel
              exact hLabel
            have hIH := ih right tail hRight hTailFields.2 childEdge hChildEdge
              hChildLabel
            refine ⟨hIH.1, ?_⟩
            have hSource : edge.source =
                TypeAutomatonState.child 1 childEdge.source := by
              rw [← hEq]; rfl
            rw [hSource]
            exact TypeCompilationRelation.sequence_right left right
              (PactType.var name) childEdge.source hIH.2
          · exfalso
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
      | par left right interface =>
          exfalso
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences name False left ∧
              PactType.TailOccurrences name False right := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hTransition | hObservation
          · rcases hTransition with
              ⟨leftEdge, ⟨hLeftEdge, _⟩, rightEdge, ⟨⟨hRightEdge, _⟩, _⟩, hEq⟩
            rw [← hEq] at hLabel
            simp only at hLabel
            have hComponent :
                leftEdge.label = AutomatonConstructionLabel.variable name ∨
                  rightEdge.label = AutomatonConstructionLabel.variable name := by
              cases hLeftLabel : leftEdge.label <;>
                cases hRightLabel : rightEdge.label <;>
                  simp_all [AutomatonConstructionLabel.combine]
            rcases hComponent with hComponent | hComponent
            · simp only [resolvedAutomatonEdges, Finset.mem_image] at hLeftEdge
              rcases hLeftEdge with ⟨raw, hRaw, hRawEq⟩
              refine (ih left False hLeft hTailFields.1 raw hRaw ?_).1
              rw [← hRawEq] at hComponent
              exact hComponent
            · simp only [resolvedAutomatonEdges, Finset.mem_image] at hRightEdge
              rcases hRightEdge with ⟨raw, hRaw, hRawEq⟩
              refine (ih right False hRight hTailFields.2 raw hRaw ?_).1
              rw [← hRawEq] at hComponent
              exact hComponent
          · rcases hObservation with hLeftFuture | hRightFuture
            · rcases hLeftFuture with ⟨leftState, _, rightState, _, hEq⟩
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
            · rcases hRightFuture with ⟨leftState, _, rightState, _, hEq⟩
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
      | xoffer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hBranches : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hTailFields : PactType.TailOccurrences name tail elseType ∧
              PactType.TailBranchOccurrences name tail branches := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with
            ((((hElseEdge | hIndexed) | hBranch) | hWait) | hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
            rcases hElseEdge with ⟨childEdge, hChildEdge, hEq⟩
            have hChildLabel :
                childEdge.label = AutomatonConstructionLabel.variable name := by
              rw [← hEq] at hLabel
              exact hLabel
            have hIH := ih elseType tail hElse hTailFields.1 childEdge
              hChildEdge hChildLabel
            refine ⟨hIH.1, ?_⟩
            have hSource : edge.source =
                TypeAutomatonState.child 0 childEdge.source := by
              rw [← hEq]; rfl
            rw [hSource]
            exact TypeCompilationRelation.xoffer_else elseType
              (PactType.var name) branches childEdge.source hIH.2
          · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨childEdge, hChildEdge, hEq⟩
              have hIndexedFields := List.mem_zipIdx hIndexedMem
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                at hIndexedFields
              rcases hIndexedFields with ⟨hBound, hValue⟩
              have hIndexedEntry :
                  (branches.map fun branch =>
                    (branch.1, compileTypeFuel signature fuel
                      branch.2))[indexed.2]? = some indexed.1 := by
                rw [List.getElem?_eq_getElem hBound, ← hValue]
              rw [List.getElem?_map] at hIndexedEntry
              rcases Option.map_eq_some_iff.mp hIndexedEntry with
                ⟨entry, hEntry, hEntryEq⟩
              have hChildLabel :
                  childEdge.label =
                    AutomatonConstructionLabel.variable name := by
                rw [← hEq] at hLabel
                exact hLabel
              have hEntryMem : entry ∈ branches :=
                List.mem_of_getElem? hEntry
              have hEntryFuel :
                  TypeCompilationFuelSufficient entry.2 fuel :=
                le_trans (typeCompilationFuel_le_typeBranchCompilationFuel
                  branches entry hEntryMem) hBranches
              have hFragmentEq :
                  indexed.1.2 = compileTypeFuel signature fuel entry.2 := by
                rw [← hEntryEq]
              rw [hFragmentEq] at hChildEdge
              have hIH := ih entry.2 tail hEntryFuel
                (tailBranchOccurrences_mem name tail branches entry
                  hTailFields.2 hEntryMem) childEdge hChildEdge hChildLabel
              refine ⟨hIH.1, ?_⟩
              have hSource : edge.source =
                  TypeAutomatonState.child (indexed.2 + 1) childEdge.source := by
                rw [← hEq]; rfl
              rw [hSource]
              exact TypeCompilationRelation.xoffer_branch elseType entry.2
                (PactType.var name) branches entry.1 indexed.2
                childEdge.source hEntry hIH.2
          · rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
            · simp at hEmpty
            · exfalso
              simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
              rcases hNewEdge with ⟨environment, _, hEq⟩
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨environment, _, hEq⟩
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨environment, _, hEq⟩
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
      | offer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hConjunction : conjunctiveCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hTailFields : PactType.TailOccurrences name tail elseType ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with
            ((((hElseEdge | hIndexed) | hEnabled) | hWait) | hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
            rcases hElseEdge with ⟨childEdge, hChildEdge, hEq⟩
            have hChildLabel :
                childEdge.label = AutomatonConstructionLabel.variable name := by
              rw [← hEq] at hLabel
              exact hLabel
            have hIH := ih elseType tail hElse hTailFields.1 childEdge
              hChildEdge hChildLabel
            refine ⟨hIH.1, ?_⟩
            have hSource : edge.source =
                TypeAutomatonState.child 0 childEdge.source := by
              rw [← hEq]; rfl
            rw [hSource]
            exact TypeCompilationRelation.offer_else elseType
              (PactType.var name) branches childEdge.source hIH.2
          · exfalso
            rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨childEdge, hChildEdge, hEq⟩
              have hIndexedFields := List.mem_zipIdx hIndexedMem
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                at hIndexedFields
              rcases hIndexedFields with ⟨hBound, hValue⟩
              have hIndexedEntry :
                  (branches.map fun selected =>
                    (selected.1, compileTypeFuel signature fuel
                      (parallelTypeBranchesSelecting selected
                        branches)))[indexed.2]? = some indexed.1 := by
                rw [List.getElem?_eq_getElem hBound, ← hValue]
              rw [List.getElem?_map] at hIndexedEntry
              rcases Option.map_eq_some_iff.mp hIndexedEntry with
                ⟨entry, hEntry, hEntryEq⟩
              have hChildLabel :
                  childEdge.label =
                    AutomatonConstructionLabel.variable name := by
                rw [← hEq] at hLabel
                exact hLabel
              have hSelectedFuel : TypeCompilationFuelSufficient
                  (parallelTypeBranchesSelecting entry branches) fuel := by
                have := typeCompilationFuel_parallelTypeBranchesSelecting entry
                  branches
                simp only [TypeCompilationFuelSufficient, this]
                exact hConjunction
              have hFragmentEq : indexed.1.2 = compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting entry branches) := by
                rw [← hEntryEq]
              rw [hFragmentEq] at hChildEdge
              exact (ih (parallelTypeBranchesSelecting entry branches) False
                hSelectedFuel
                (tailOccurrences_parallelTypeBranchesSelecting name entry
                  branches hTailFields.2) childEdge hChildEdge hChildLabel).1
          · exfalso
            rw [mem_foldl_union_iff] at hEnabled
            rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
              rcases hNewEdge with ⟨environment, _, hEq⟩
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨environment, _, hEq⟩
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨environment, _, hEq⟩
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)

/-- Every `.variable name` marker edge the compiler produces is inert: it
offers nothing in the current cycle and refers to nothing later.  Markers are
therefore invisible to `computeFuture` until an enclosing recursion binder
installs their backedges — which is exactly the `MarkerEdgesInert` hypothesis
of `mem_computeFuture_markerAugmented`.

The `TailOccurrences` premise is genuinely needed rather than bookkeeping:
`AutomatonConstructionLabel.combine` propagates a component `.variable name`
label onto a synchronized product edge, and that edge carries real product
offers.  Tail occurrence rules out a marker below `par` (and below a
conjunctive-offer branch) in the first place, which is why those two cases are
vacuous instead of structural. -/
theorem compileTypeFuel_markerEdgesInert
    (signature : TypeAlphabet) (name : String) :
    ∀ (fuel : Nat) (processType : PactType) (tail : Prop),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailOccurrences name tail processType →
        MarkerEdgesInert (compileTypeFuel signature fuel processType) name := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType tail hFuel hTail edge hEdge _
      simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
      intro processType tail hFuel hTail edge hEdge hLabel
      cases processType with
      | skip =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩
          rw [← hEq] at hLabel
          exact absurd hLabel (by simp)
      | message msg dir =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ((⟨e, _, hEq⟩ | ⟨e, _, hEq⟩) | ⟨e, _, hEq⟩) <;>
            (rw [← hEq] at hLabel; exact absurd hLabel (by simp))
      | tock =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨e, _, hEq⟩ | ⟨e, _, hEq⟩)
          · rw [← hEq] at hLabel
            split at hLabel <;> exact absurd hLabel (by simp)
          · rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
      | progress pid =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨e, _, hEq⟩ | ⟨e, _, hEq⟩) <;>
            (rw [← hEq] at hLabel; exact absurd hLabel (by simp))
      | var other =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩
          rw [← hEq]
          exact ⟨rfl, rfl⟩
      | recur other body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
            at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩ | ⟨bodyEdge, hBodyEdge, hEq⟩
          · exfalso
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
          · by_cases hVarOther :
                bodyEdge.label = AutomatonConstructionLabel.variable other
            · exfalso
              rw [if_pos hVarOther] at hEq
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
            · rw [if_neg hVarOther] at hEq
              have hBodyLabel :
                  bodyEdge.label = AutomatonConstructionLabel.variable name := by
                rw [← hEq] at hLabel
                exact hLabel
              have hOther : other ≠ name := by
                intro hEqName
                exact hVarOther (hEqName ▸ hBodyLabel)
              have hTailBody : PactType.TailOccurrences name tail body := by
                have hTail' := hTail
                simp only [PactType.TailOccurrences] at hTail'
                rw [if_neg hOther] at hTail'
                exact hTail'
              have hIH := ih body tail hBody hTailBody bodyEdge hBodyEdge
                hBodyLabel
              rw [← hEq]
              exact ⟨hIH.1, by simp [hIH.2, childFutureSpec]⟩
      | choice left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences name tail left ∧
              PactType.TailOccurrences name tail right := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton] at hEdge
          rcases hEdge with (⟨childEdge, hChildEdge, hEq⟩ |
            ⟨childEdge, hChildEdge, hEq⟩) | ⟨environment, _, hEq | hEq⟩
          · have hIH := ih left tail hLeft hTailFields.1 childEdge hChildEdge
              (by rw [← hEq] at hLabel; exact hLabel)
            rw [← hEq]
            exact ⟨hIH.1, by simp [hIH.2, childPendingEdge, childFutureSpec]⟩
          · have hIH := ih right tail hRight hTailFields.2 childEdge hChildEdge
              (by rw [← hEq] at hLabel; exact hLabel)
            rw [← hEq]
            exact ⟨hIH.1, by simp [hIH.2, childPendingEdge, childFutureSpec]⟩
          · exfalso
            rw [hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            rw [hEq] at hLabel
            exact absurd hLabel (by simp)
      | fairChoice bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences name tail left ∧
              PactType.TailOccurrences name tail right := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton] at hEdge
          rcases hEdge with (⟨childEdge, hChildEdge, hEq⟩ |
            ⟨childEdge, hChildEdge, hEq⟩) | ⟨environment, _, hEq | hEq⟩
          · have hIH := ih left tail hLeft hTailFields.1 childEdge hChildEdge
              (by rw [← hEq] at hLabel; exact hLabel)
            rw [← hEq]
            exact ⟨hIH.1, by simp [hIH.2, childPendingEdge, childFutureSpec]⟩
          · have hIH := ih right tail hRight hTailFields.2 childEdge hChildEdge
              (by rw [← hEq] at hLabel; exact hLabel)
            rw [← hEq]
            exact ⟨hIH.1, by simp [hIH.2, childPendingEdge, childFutureSpec]⟩
          · exfalso
            rw [hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            rw [hEq] at hLabel
            exact absurd hLabel (by simp)
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences name False left ∧
              PactType.TailOccurrences name tail right := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion] at hEdge
          rcases hEdge with ((⟨childEdge, hChildEdge, hEq⟩ |
              ⟨childEdge, hChildEdge, hEq⟩) |
            ⟨skipState, _, environment, _, hEq⟩) | ⟨completeState, _, hEq⟩
          · -- A lifted *left* sequence edge is re-decorated with a symbolic
            -- `.at` future at its tagged target, so it would not be inert.
            -- `TailOccurrences` forbids `name` in a sequence's left component
            -- outright, so this case is vacuous rather than structural.
            exact (compileTypeFuel_variableEdge_source_var signature name
              fuel left False hLeft hTailFields.1 childEdge hChildEdge
              (by rw [← hEq] at hLabel; exact hLabel)).1.elim
          · have hIH := ih right tail hRight hTailFields.2 childEdge hChildEdge
              (by rw [← hEq] at hLabel; exact hLabel)
            rw [← hEq]
            exact ⟨hIH.1, by simp [hIH.2, childPendingEdge, childFutureSpec]⟩
          · exfalso
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
      | par left right interface =>
          exfalso
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences name False left ∧
              PactType.TailOccurrences name False right := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hTransition | hObservation
          · rcases hTransition with
              ⟨leftEdge, ⟨hLeftEdge, _⟩, rightEdge, ⟨⟨hRightEdge, _⟩, _⟩, hEq⟩
            rw [← hEq] at hLabel
            simp only at hLabel
            have hComponent :
                leftEdge.label = AutomatonConstructionLabel.variable name ∨
                  rightEdge.label = AutomatonConstructionLabel.variable name := by
              cases hLeftLabel : leftEdge.label <;>
                cases hRightLabel : rightEdge.label <;>
                  simp_all [AutomatonConstructionLabel.combine]
            rcases hComponent with hComponent | hComponent
            · simp only [resolvedAutomatonEdges, Finset.mem_image] at hLeftEdge
              rcases hLeftEdge with ⟨raw, hRaw, hRawEq⟩
              refine (compileTypeFuel_variableEdge_source_var signature name
                fuel left False hLeft hTailFields.1 raw hRaw ?_).1
              rw [← hRawEq] at hComponent
              exact hComponent
            · simp only [resolvedAutomatonEdges, Finset.mem_image] at hRightEdge
              rcases hRightEdge with ⟨raw, hRaw, hRawEq⟩
              refine (compileTypeFuel_variableEdge_source_var signature name
                fuel right False hRight hTailFields.2 raw hRaw ?_).1
              rw [← hRawEq] at hComponent
              exact hComponent
          · rcases hObservation with hLeftFuture | hRightFuture
            · rcases hLeftFuture with ⟨leftState, _, rightState, _, hEq⟩
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
            · rcases hRightFuture with ⟨leftState, _, rightState, _, hEq⟩
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
      | xoffer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hBranches : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hTailFields : PactType.TailOccurrences name tail elseType ∧
              PactType.TailBranchOccurrences name tail branches := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with
            ((((hElseEdge | hIndexed) | hBranch) | hWait) | hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
            rcases hElseEdge with ⟨childEdge, hChildEdge, hEq⟩
            have hIH := ih elseType tail hElse hTailFields.1 childEdge
              hChildEdge (by rw [← hEq] at hLabel; exact hLabel)
            rw [← hEq]
            exact ⟨hIH.1, by simp [hIH.2, childPendingEdge, childFutureSpec]⟩
          · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨childEdge, hChildEdge, hEq⟩
              have hIndexedFields := List.mem_zipIdx hIndexedMem
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                at hIndexedFields
              rcases hIndexedFields with ⟨hBound, hValue⟩
              have hIndexedEntry :
                  (branches.map fun branch =>
                    (branch.1, compileTypeFuel signature fuel
                      branch.2))[indexed.2]? = some indexed.1 := by
                rw [List.getElem?_eq_getElem hBound, ← hValue]
              rw [List.getElem?_map] at hIndexedEntry
              rcases Option.map_eq_some_iff.mp hIndexedEntry with
                ⟨entry, hEntry, hEntryEq⟩
              have hEntryMem : entry ∈ branches :=
                List.mem_of_getElem? hEntry
              have hEntryFuel :
                  TypeCompilationFuelSufficient entry.2 fuel :=
                le_trans (typeCompilationFuel_le_typeBranchCompilationFuel
                  branches entry hEntryMem) hBranches
              have hFragmentEq :
                  indexed.1.2 = compileTypeFuel signature fuel entry.2 := by
                rw [← hEntryEq]
              rw [hFragmentEq] at hChildEdge
              have hIH := ih entry.2 tail hEntryFuel
                (tailBranchOccurrences_mem name tail branches entry
                  hTailFields.2 hEntryMem) childEdge hChildEdge
                (by rw [← hEq] at hLabel; exact hLabel)
              rw [← hEq]
              exact ⟨hIH.1, by simp [hIH.2, childPendingEdge, childFutureSpec]⟩
          · exfalso
            rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
              rcases hNewEdge with ⟨environment, _, hEq⟩
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨environment, _, hEq⟩
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨environment, _, hEq⟩
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
      | offer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hConjunction : conjunctiveCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hTailFields : PactType.TailOccurrences name tail elseType ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with
            ((((hElseEdge | hIndexed) | hEnabled) | hWait) | hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
            rcases hElseEdge with ⟨childEdge, hChildEdge, hEq⟩
            have hIH := ih elseType tail hElse hTailFields.1 childEdge
              hChildEdge (by rw [← hEq] at hLabel; exact hLabel)
            rw [← hEq]
            exact ⟨hIH.1, by simp [hIH.2, childPendingEdge, childFutureSpec]⟩
          · exfalso
            rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨childEdge, hChildEdge, hEq⟩
              have hIndexedFields := List.mem_zipIdx hIndexedMem
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                at hIndexedFields
              rcases hIndexedFields with ⟨hBound, hValue⟩
              have hIndexedEntry :
                  (branches.map fun selected =>
                    (selected.1, compileTypeFuel signature fuel
                      (parallelTypeBranchesSelecting selected
                        branches)))[indexed.2]? = some indexed.1 := by
                rw [List.getElem?_eq_getElem hBound, ← hValue]
              rw [List.getElem?_map] at hIndexedEntry
              rcases Option.map_eq_some_iff.mp hIndexedEntry with
                ⟨entry, hEntry, hEntryEq⟩
              have hSelectedFuel : TypeCompilationFuelSufficient
                  (parallelTypeBranchesSelecting entry branches) fuel := by
                have := typeCompilationFuel_parallelTypeBranchesSelecting entry
                  branches
                simp only [TypeCompilationFuelSufficient, this]
                exact hConjunction
              have hFragmentEq : indexed.1.2 = compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting entry branches) := by
                rw [← hEntryEq]
              rw [hFragmentEq] at hChildEdge
              exact (compileTypeFuel_variableEdge_source_var signature name fuel
                (parallelTypeBranchesSelecting entry branches) False
                hSelectedFuel
                (tailOccurrences_parallelTypeBranchesSelecting name entry
                  branches hTailFields.2) childEdge hChildEdge
                (by rw [← hEq] at hLabel; exact hLabel)).1
          · exfalso
            rw [mem_foldl_union_iff] at hEnabled
            rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
              rcases hNewEdge with ⟨environment, _, hEq⟩
              rw [← hEq] at hLabel
              exact absurd hLabel (by simp)
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨environment, _, hEq⟩
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨environment, _, hEq⟩
            rw [← hEq] at hLabel
            exact absurd hLabel (by simp)

end

end Pact
