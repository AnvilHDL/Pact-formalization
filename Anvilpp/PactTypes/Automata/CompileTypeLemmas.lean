import Anvilpp.PactTypes.Automata.CompileTypeDefs

namespace Pact

noncomputable section

theorem typeCompilationFuel_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    typeCompilationFuel (processType.reannotate alphabet) =
      typeCompilationFuel processType := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType alphabet with
  | _ n ih =>
      have hBranch : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ branchAlphabet,
          typeBranchCompilationFuel
              (PactType.reannotateBranches branchAlphabet branches) =
            typeBranchCompilationFuel branches := by
        intro branches hBranches branchAlphabet
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            typeBranchCompilationFuel]
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
              typeBranchCompilationFuel]
            rw [ih (sizeOf branchType) hType branchAlphabet branchType rfl,
              restIH hRest]
      have hConj : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ branchAlphabet,
          conjunctiveCompilationFuel
              (PactType.reannotateBranches branchAlphabet branches) =
            conjunctiveCompilationFuel branches := by
        intro branches hBranches branchAlphabet
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            conjunctiveCompilationFuel]
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
            cases rest with
            | nil =>
                simp [PactType.reannotateBranches,
                  conjunctiveCompilationFuel,
                  ih (sizeOf branchType) hType branchAlphabet branchType rfl]
            | cons next tail =>
                rcases next with ⟨nextAction, nextType⟩
                have hRestEq := restIH hRest
                rw [PactType.reannotateBranches_cons] at hRestEq
                rw [PactType.reannotateBranches_cons,
                  PactType.reannotateBranches_cons]
                simp only [conjunctiveCompilationFuel]
                rw [ih (sizeOf branchType) hType branchAlphabet branchType rfl,
                  hRestEq]
      have hConjOffer : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ branchAlphabet (seen : Finset BareMessage),
          conjunctiveCompilationFuel
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
            conjunctiveCompilationFuel branches := by
        intro branches hBranches branchAlphabet
        induction branches with
        | nil =>
            intro seen
            rw [PactType.reannotateOfferBranches_nil]
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
            cases rest with
            | nil =>
                rw [PactType.reannotateOfferBranches_cons,
                  PactType.reannotateOfferBranches_nil]
                simp only [conjunctiveCompilationFuel]
                rw [ih (sizeOf branchType) hType _ branchType rfl]
            | cons next tail =>
                rcases next with ⟨nextAction, nextType⟩
                have hRestEq := restIH hRest
                  (seen ∪ ({action} ∪ PactType.MessageActions branchType))
                rw [PactType.reannotateOfferBranches_cons] at hRestEq
                rw [PactType.reannotateOfferBranches_cons,
                  PactType.reannotateOfferBranches_cons]
                simp only [conjunctiveCompilationFuel]
                rw [ih (sizeOf branchType) hType _ branchType rfl, hRestEq]
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, typeCompilationFuel]
      | recur _ _ body =>
          have hBody : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, typeCompilationFuel,
            ih (sizeOf body) hBody alphabet body rfl]
      | choice _ left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, typeCompilationFuel,
            ih (sizeOf left) hLeft alphabet left rfl,
            ih (sizeOf right) hRight alphabet right rfl]
      | seq _ left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, typeCompilationFuel,
            ih (sizeOf left) hLeft alphabet left rfl,
            ih (sizeOf right) hRight alphabet right rfl]
      | fairChoice _ _ left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, typeCompilationFuel,
            ih (sizeOf left) hLeft alphabet left rfl,
            ih (sizeOf right) hRight alphabet right rfl]
      | par _ left right interface =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, typeCompilationFuel,
            ih (sizeOf left) hLeft
              (PactTypeAlphabet.projectParallelLeft alphabet left.alphabet
                right interface) left rfl,
            ih (sizeOf right) hRight
              (PactTypeAlphabet.projectParallelChild alphabet right.alphabet
                interface) right rfl]
      | xoffer _ elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranches : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, typeCompilationFuel,
            ih (sizeOf elseType) hElse alphabet elseType rfl,
            hBranch branches hBranches alphabet]
      | offer _ elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranches : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, typeCompilationFuel,
            ih (sizeOf elseType) hElse alphabet elseType rfl,
            hConjOffer branches hBranches alphabet ∅]

theorem typeCompilationFuel_parallelTypeBranchesWithin
    (alphabet : PactTypeAlphabet) : ∀ branches,
    typeCompilationFuel (parallelTypeBranchesWithin alphabet branches) =
      conjunctiveCompilationFuel branches
  | [] => by
      simp [parallelTypeBranchesWithin, typeCompilationFuel,
        conjunctiveCompilationFuel]
  | [(_, processType)] => by
      simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
        typeCompilationFuel, typeBranchCompilationFuel,
        conjunctiveCompilationFuel,
        typeCompilationFuel_reannotate]
  | (action, processType) :: next :: rest => by
      simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
        typeCompilationFuel, typeBranchCompilationFuel,
        conjunctiveCompilationFuel,
        typeCompilationFuel_reannotate,
        typeCompilationFuel_parallelTypeBranchesWithin]

theorem typeCompilationFuel_parallelTypeBranchesSelectingWithin
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches,
    typeCompilationFuel
        (parallelTypeBranchesSelectingWithin alphabet selected branches) =
      conjunctiveCompilationFuel branches
  | [] => by
      simp [parallelTypeBranchesSelectingWithin, typeCompilationFuel,
        conjunctiveCompilationFuel]
  | [branch] => by
      rcases branch with ⟨action, processType⟩
      by_cases hSelected : (action, processType) = selected
      · subst selected
        simp [parallelTypeBranchesSelectingWithin,
          selectedTypeBranchAt, typeCompilationFuel,
          conjunctiveCompilationFuel, typeCompilationFuel_reannotate]
      · simp [parallelTypeBranchesSelectingWithin, hSelected,
          singletonTypeXOfferAt, typeCompilationFuel,
          typeBranchCompilationFuel,
          conjunctiveCompilationFuel, typeCompilationFuel_reannotate]
  | (action, processType) :: next :: rest => by
      by_cases hSelected : (action, processType) = selected
      · subst selected
        simp [parallelTypeBranchesSelectingWithin,
          selectedTypeBranchAt, typeCompilationFuel,
          conjunctiveCompilationFuel, typeCompilationFuel_reannotate,
          typeCompilationFuel_parallelTypeBranchesWithin]
      · simp [parallelTypeBranchesSelectingWithin, hSelected,
          singletonTypeXOfferAt, typeCompilationFuel,
          typeBranchCompilationFuel,
          conjunctiveCompilationFuel, typeCompilationFuel_reannotate,
          typeCompilationFuel_parallelTypeBranchesSelectingWithin]

/--
The auxiliary budget is exactly the budget of the parallel type generated for
a conjunctive offer.  This is the non-structural recursive call that motivates
the custom fuel calculation.
-/
theorem typeCompilationFuel_parallelTypeBranches
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType)) :
    typeCompilationFuel (parallelTypeBranches alphabet branches) =
      conjunctiveCompilationFuel branches := by
  cases branches with
  | nil => simp [parallelTypeBranches, typeCompilationFuel,
      conjunctiveCompilationFuel]
  | cons branch rest =>
      exact typeCompilationFuel_parallelTypeBranchesWithin
        alphabet (branch :: rest)

/-- Forcing one singleton branch removes only its synthetic else outcome and
does not change the compilation budget of the generated parallel product. -/
theorem typeCompilationFuel_parallelTypeBranchesSelecting
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    typeCompilationFuel
        (parallelTypeBranchesSelecting alphabet selected branches) =
      conjunctiveCompilationFuel branches := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, typeCompilationFuel,
      conjunctiveCompilationFuel]
  | cons branch rest =>
      exact typeCompilationFuel_parallelTypeBranchesSelectingWithin
        alphabet selected (branch :: rest)

/-- The calculated compilation budget is sufficient by construction. -/
theorem typeCompilationFuel_sufficient (processType : PactType) :
    TypeCompilationFuelSufficient processType
      (typeCompilationFuel processType) := by
  exact le_rfl

/-- Every type receives at least the one unit needed to enter its constructor. -/
theorem typeCompilationFuel_positive (processType : PactType) :
    0 < typeCompilationFuel processType := by
  cases processType <;> simp [typeCompilationFuel] <;> omega

/-- Sufficient fuel can never select the defensive zero-fuel case at the root. -/
theorem TypeCompilationFuelSufficient.positive
    {processType : PactType} {fuel : Nat}
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    0 < fuel :=
  lt_of_lt_of_le (typeCompilationFuel_positive processType) hFuel

theorem typeCompilationFuel_le_typeBranchCompilationFuel
    (branches : List (BareMessage × PactType))
    (entry : BareMessage × PactType) (hEntry : entry ∈ branches) :
    typeCompilationFuel entry.2 ≤ typeBranchCompilationFuel branches := by
  induction branches with
  | nil => simp at hEntry
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · simp [typeBranchCompilationFuel]
      · exact le_trans (ih hRest) (by
          simp [typeBranchCompilationFuel])

/-- Every continuation in a conjunctive offer fits within the compilation
budget of the generated branch product. -/
theorem typeCompilationFuel_le_conjunctiveCompilationFuel
    (branches : List (BareMessage × PactType))
    (entry : BareMessage × PactType) (hEntry : entry ∈ branches) :
    typeCompilationFuel entry.2 ≤ conjunctiveCompilationFuel branches := by
  induction branches with
  | nil => simp at hEntry
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      simp only [List.mem_cons] at hEntry
      cases rest with
      | nil =>
          have hEq : entry = (action, processType) := by
            simpa using hEntry
          subst entry
          simp [conjunctiveCompilationFuel]
          omega
      | cons next tail =>
          rcases hEntry with hHead | hRest
          · subst entry
            simp [conjunctiveCompilationFuel]
            omega
          · exact le_trans (ih hRest) (by
              simp [conjunctiveCompilationFuel]
              omega)

/-- A sufficient parent budget gives a child exactly its public, type-aware
future function. -/
theorem compiledChildFutureFuel_eq_computeFutureOf
     (fuel : Nat) (processType : PactType)
    (hFuel : typeCompilationFuel processType ≤ fuel) :
    compiledChildFutureFuel fuel processType =
      computeFutureOfFuel (typeCompilationFuel processType)
        processType := by
  unfold compiledChildFutureFuel
  rw [Nat.min_eq_right hFuel]

/-- Once fuel covers the custom compilation budget, one more unit leaves the
constructor fragment unchanged. -/
private theorem compileTypeFuel_succ_stable :
    ∀ fuel  processType,
      typeCompilationFuel processType ≤ fuel →
      compileTypeFuel (fuel + 1) processType =
        compileTypeFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      have hPositive := typeCompilationFuel_positive processType
      omega
  | succ fuel ih =>
      intro processType hFuel
      conv_lhs => rw [compileTypeFuel.eq_def]
      conv_rhs => rw [compileTypeFuel.eq_def]
      cases processType with
      | message alphabet msg dir => rfl
      | progress alphabet pid => rfl
      | tock alphabet => rfl
      | skip alphabet => rfl
      | var alphabet name => rfl
      | recur alphabet name body =>
          change buildRecursionAutomaton alphabet name
              (compileTypeFuel (fuel + 1) body) =
            buildRecursionAutomaton alphabet name
              (compileTypeFuel fuel body)
          rw [ih body (by
            simp [typeCompilationFuel] at hFuel
            omega)]
      | choice alphabet left right =>
          change buildChoiceAutomaton alphabet
              (compileTypeFuel (fuel + 1) left)
              (compileTypeFuel (fuel + 1) right)
              TypeLabel.silent TypeLabel.silent =
            buildChoiceAutomaton alphabet
              (compileTypeFuel fuel left)
              (compileTypeFuel fuel right)
              TypeLabel.silent TypeLabel.silent
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | fairChoice alphabet bid left right =>
          change buildChoiceAutomaton alphabet
              (compileTypeFuel (fuel + 1) left)
              (compileTypeFuel (fuel + 1) right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
            buildChoiceAutomaton alphabet
              (compileTypeFuel fuel left)
              (compileTypeFuel fuel right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | seq alphabet left right =>
          change buildSequenceAutomaton
              (compileTypeFuel (fuel + 1) left)
              (compileTypeFuel (fuel + 1) right) =
            buildSequenceAutomaton
              (compileTypeFuel fuel left)
              (compileTypeFuel fuel right)
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | par alphabet left right interface =>
          change buildParallelAutomaton alphabet left.alphabet
              right.alphabet interface
              (compileTypeFuel (fuel + 1) left)
              (compileTypeFuel (fuel + 1) right)
              (compileTypeFuel (fuel + 1) (left.reannotate alphabet))
              (compileTypeFuel (fuel + 1) (right.reannotate alphabet))
              (computeFutureOfFuel
                (min (fuel + 1) (typeCompilationFuel left)) left)
              (computeFutureOfFuel
                (min (fuel + 1) (typeCompilationFuel right)) right)
              (computeFutureOfFuel
                (min (fuel + 1) (typeCompilationFuel left)) (left.reannotate alphabet))
              (computeFutureOfFuel
                (min (fuel + 1) (typeCompilationFuel right)) (right.reannotate alphabet)) =
            buildParallelAutomaton alphabet left.alphabet
              right.alphabet interface
              (compileTypeFuel fuel left)
              (compileTypeFuel fuel right)
              (compileTypeFuel fuel (left.reannotate alphabet))
              (compileTypeFuel fuel (right.reannotate alphabet))
              (computeFutureOfFuel
                (min fuel (typeCompilationFuel left)) left)
              (computeFutureOfFuel
                (min fuel (typeCompilationFuel right)) right)
              (computeFutureOfFuel
                (min fuel (typeCompilationFuel left)) (left.reannotate alphabet))
              (computeFutureOfFuel
                (min fuel (typeCompilationFuel right)) (right.reannotate alphabet))
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          simp only [Nat.min_eq_right hLeft, Nat.min_eq_right (Nat.le.step hLeft),
            Nat.min_eq_right hRight, Nat.min_eq_right (Nat.le.step hRight)]
          rw [ih left (by
              exact hLeft),
            ih right (by
              exact hRight),
            ih (left.reannotate alphabet) (by
              rw [typeCompilationFuel_reannotate]; exact hLeft),
            ih (right.reannotate alphabet) (by
              rw [typeCompilationFuel_reannotate]; exact hRight)]
      | xoffer alphabet elseType branches =>
          change buildExclusiveOfferAutomaton alphabet branches
              (compileTypeFuel
                (fuel + 1) elseType)
              (branches.map fun branch =>
                (branch.1, compileTypeFuel
                  (fuel + 1) branch.2)) =
            buildExclusiveOfferAutomaton alphabet branches
              (compileTypeFuel fuel elseType)
              (branches.map fun branch =>
                (branch.1, compileTypeFuel
                  fuel branch.2))
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          rw [ih elseType hElse]
          congr 1
          have hBranches : typeBranchCompilationFuel branches ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          have hMap : ∀ rest,
              typeBranchCompilationFuel rest ≤ fuel →
              (rest.map fun branch =>
                (branch.1, compileTypeFuel
                  (fuel + 1) branch.2)) =
              (rest.map fun branch =>
                (branch.1, compileTypeFuel
                  fuel branch.2)) := by
            intro rest
            induction rest with
            | nil => simp
            | cons branch tail tailIH =>
                intro hRest
                rcases branch with ⟨action, branchType⟩
                simp only [List.map_cons]
                have hBranch : typeCompilationFuel branchType ≤ fuel := by
                  simp [typeBranchCompilationFuel] at hRest
                  omega
                rw [ih branchType hBranch]
                congr 1
                apply tailIH
                simp [typeBranchCompilationFuel] at hRest ⊢
                omega
          exact hMap branches hBranches
      | offer alphabet elseType branches =>
          change buildSelectedConjunctiveOfferAutomaton alphabet
              branches
              (compileTypeFuel
                (fuel + 1) elseType)
              (branches.map fun selected =>
                (selected.1,
                  compileTypeFuel
                   
                    (fuel + 1)
                    (parallelTypeBranchesSelecting alphabet selected
                      branches))) =
            buildSelectedConjunctiveOfferAutomaton alphabet branches
              (compileTypeFuel fuel elseType)
              (branches.map fun selected =>
                (selected.1,
                  compileTypeFuel
                   
                    fuel
                    (parallelTypeBranchesSelecting alphabet selected
                      branches)))
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          rw [ih elseType hElse]
          congr 1
          apply List.map_congr_left
          intro selected hSelected
          congr 1
          apply ih
          rw [typeCompilationFuel_parallelTypeBranchesSelecting]
          simp [typeCompilationFuel] at hFuel
          omega

/-- Any two sufficient parent budgets produce the same constructor fragment. -/
private theorem compileTypeFuel_add_stable
     (processType : PactType)
    (fuel extra : Nat) (hFuel : typeCompilationFuel processType ≤ fuel) :
    compileTypeFuel (fuel + extra) processType =
      compileTypeFuel fuel processType := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        compileTypeFuel_succ_stable (fuel + extra) processType
          (by omega),
        ih]

theorem compileTypeFuel_eq_of_sufficient
     (processType : PactType)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    compileTypeFuel leftFuel processType =
      compileTypeFuel rightFuel processType := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (compileTypeFuel_add_stable processType leftFuel extra
      hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact compileTypeFuel_add_stable processType rightFuel extra hRight

@[simp] theorem compileType_alphabet
     (processType : PactType) :
    (compileType processType).alphabet =
      processType.transitionAlphabet := by
  rfl

/-- Public edge membership is exactly resolved membership in the constructor
fragment. -/
theorem compileType_hasEdge_iff_hasResolvedEdge
     (processType : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileType processType).HasEdge source env label offers target ↔
      AutomatonFragment.HasResolvedEdge
        processType
        (compileTypeFuel
          (typeCompilationFuel processType) processType)
        source env label offers target := by
  classical
  simp [TypeAutomaton.HasEdge, compileType,
    AutomatonFragment.HasResolvedEdge, resolvedAutomatonEdges,
    resolveAutomatonEdgesWith]
  aesop

/-- A public edge is equivalently the corresponding resolved fragment edge. -/
theorem compileType_hasEdge_iff_resolvedEdge_mem
     (processType : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileType processType).HasEdge source env label offers target ↔
      ({ source := source,
          environment := env,
          label := .visible label,
          current := offers.current,
          future := offers.future,
          target := target } : AutomatonFragmentEdge) ∈
        resolveAutomatonEdgesWith
          (compileTypeFuel
            (typeCompilationFuel processType) processType)
          (computeFutureOf
            processType) := by
  rw [compileType_hasEdge_iff_hasResolvedEdge processType source
    target env label offers]
  simp [AutomatonFragment.HasResolvedEdge, resolveAutomatonEdgesWith]
  aesop

/-- The source of every compiled transition belongs to the exported state
carrier. -/
theorem compileType_edge_source_mem
     (processType : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType processType).HasEdge
      source env label offers target) :
    source ∈ (compileType processType).states := by
  simp only [TypeAutomaton.HasEdge] at hEdge
  simp only [compileType, Finset.mem_union]
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨
    { source := source
      symbol := { environment := env, label := label, offers := offers }
      target := target }, hEdge, ?_⟩
  simp

/-- The target of every compiled transition belongs to the exported state
carrier. -/
theorem compileType_edge_target_mem
     (processType : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType processType).HasEdge
      source env label offers target) :
    target ∈ (compileType processType).states := by
  simp only [TypeAutomaton.HasEdge] at hEdge
  simp only [compileType, Finset.mem_union]
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨
    { source := source
      symbol := { environment := env, label := label, offers := offers }
      target := target }, hEdge, ?_⟩
  simp

/-- Every sufficiently fuelled fragment contains its distinguished entry state. -/
theorem compileTypeFuel_initial_mem  :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      (compileTypeFuel fuel processType).initial ∈
        (compileTypeFuel fuel processType).states := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message alphabet msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress alphabet pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | tock alphabet =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | skip alphabet =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | var alphabet name =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | recur alphabet name body =>
          simp [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment]
      | choice alphabet left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | fairChoice alphabet bid left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | seq alphabet left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hInitial :
              (compileTypeFuel fuel left).initial ∈
                (compileTypeFuel fuel left).states :=
            ih left hLeft
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState,
            initial_not_mem_sequenceDeleted] using hInitial
      | par alphabet left right interface =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hLeftMem := ih left hLeft
          have hRightMem := ih right hRight
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_insert]
          refine Or.inr (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_biUnion.mpr ⟨_, hLeftMem, ?_⟩)))
          exact Finset.mem_image.mpr ⟨_, hRightMem, rfl⟩
      | xoffer alphabet elseType branches =>
          simp [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
      | offer alphabet elseType branches =>
          simp [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]

/-- The initial state exposed by the public compiler belongs to its state set. -/
theorem compileType_initial_mem
     (processType : PactType) :
    (compileType processType).initial ∈
      (compileType processType).states := by
  simp only [compileType, Finset.mem_union]
  left
  apply compileTypeFuel_initial_mem
  exact typeCompilationFuel_sufficient processType

end

end Pact
