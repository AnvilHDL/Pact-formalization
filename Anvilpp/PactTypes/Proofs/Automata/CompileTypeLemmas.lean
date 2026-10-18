import Anvilpp.PactTypes.Spec.Automata.CompileTypeDefs

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
        | nil => simp [typeBranchCompilationFuel]
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
        | nil => simp [conjunctiveCompilationFuel]
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
                simp [conjunctiveCompilationFuel,
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
                have hRestEq := restIH hRest seen
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
              (PactTypeAlphabet.projectParallel alphabet left.alphabet interface) left rfl,
            ih (sizeOf right) hRight
              (PactTypeAlphabet.projectParallel alphabet right.alphabet interface) right rfl]
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

/-- Consuming heads cannot increase the compilation budget of the optional product. -/
theorem typeCompilationFuel_parallelTypeBranchesFiringFrom (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (index : Nat) (branches : List (BareMessage × PactType)) :
    typeCompilationFuel (parallelTypeBranchesFiringFrom alphabet selected index branches) ≤
      conjunctiveCompilationFuel branches := by
  induction branches generalizing index with
  | nil => simp [parallelTypeBranchesFiringFrom, typeCompilationFuel, conjunctiveCompilationFuel]
  | cons branch rest ih =>
      rcases branch with ⟨action, body⟩
      cases rest with
      | nil =>
          by_cases hSelected : index ∈ selected <;>
            simp [parallelTypeBranchesFiringFrom, hSelected, singletonTypeXOfferAt,
              typeCompilationFuel, typeBranchCompilationFuel, conjunctiveCompilationFuel,
              typeCompilationFuel_reannotate]
          omega
      | cons next rest =>
          have hRest := ih (index + 1)
          by_cases hSelected : index ∈ selected <;>
            simp only [parallelTypeBranchesFiringFrom, hSelected, if_true, if_false,
              singletonTypeXOfferAt, typeCompilationFuel, typeBranchCompilationFuel,
              conjunctiveCompilationFuel, typeCompilationFuel_reannotate] <;> omega

theorem typeCompilationFuel_parallelTypeBranchesFiring (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (branches : List (BareMessage × PactType)) :
    typeCompilationFuel (parallelTypeBranchesFiring alphabet selected branches) ≤
      conjunctiveCompilationFuel branches :=
  typeCompilationFuel_parallelTypeBranchesFiringFrom alphabet selected 0 branches

/-- Every generated residual lies below its enclosing offer in the compilation induction. -/
theorem typeCompilationFuel_firing_lt_offer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (selected : Finset Nat) (branches : List (BareMessage × PactType)) :
    typeCompilationFuel (parallelTypeBranchesFiring alphabet selected branches) <
      typeCompilationFuel (.offer alphabet elseType branches) := by
  have hBound := typeCompilationFuel_parallelTypeBranchesFiring alphabet selected branches
  simp only [typeCompilationFuel]
  omega

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
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          simp only [Nat.min_eq_right hLeft,
            Nat.min_eq_right (Nat.le.step hLeft)]
          rw [ih left hLeft, ih right hRight]
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
          change buildAtomicConjunctiveOfferAutomaton alphabet
              branches
              (compileTypeFuel
                (fuel + 1) elseType)
              ((conjunctiveSelections branches.length).toList.map fun selected =>
                (selected,
                  compileTypeFuel
                   
                    (fuel + 1)
                    (parallelTypeBranchesFiring alphabet selected
                      branches))) =
            buildAtomicConjunctiveOfferAutomaton alphabet branches
              (compileTypeFuel fuel elseType)
              ((conjunctiveSelections branches.length).toList.map fun selected =>
                (selected,
                  compileTypeFuel
                   
                    fuel
                    (parallelTypeBranchesFiring alphabet selected
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
          apply le_trans (typeCompilationFuel_parallelTypeBranchesFiring alphabet selected branches)
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
    resolveAutomatonEdgesWith, resolveFutureSpec]
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
  simp [AutomatonFragment.HasResolvedEdge, resolveAutomatonEdgesWith, resolveFutureSpec]
  aesop

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
          simp [compileTypeFuel, buildAtomicConjunctiveOfferAutomaton, conjunctiveFiringEdges,
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


/-- Every stored menu a compiled fragment writes on an edge is empty: the
compiler records a same-cycle continuation symbolically, and reserves the
explicit form for edges that end the cycle or idle in place. -/
def AutomatonFragment.StoredMenusEmpty (fragment : AutomatonFragment) : Prop :=
  ∀ edge ∈ fragment.edges, ∀ offers,
    edge.future = FutureSpec.explicit offers → offers = ∅

/-- Re-tagging a child edge for an enclosing constructor never turns a
symbolic continuation into a stored one, nor enlarges a stored one. -/
theorem childFutureSpec_explicit (index : Nat) (spec : FutureSpec)
    (offers : Finset BareMessage)
    (hSpec : childFutureSpec index spec = FutureSpec.explicit offers) :
    spec = FutureSpec.explicit offers := by
  cases spec with
  | explicit inner => simpa [childFutureSpec] using hSpec
  | «at» state removed => simp [childFutureSpec] at hSpec
  | atUnion inner state removed => simp [childFutureSpec] at hSpec

/-- A copied child fragment keeps the invariant. -/
theorem childPendingEdges_storedMenusEmpty (index : Nat)
    (child : AutomatonFragment) (hChild : child.StoredMenusEmpty)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ childPendingEdges index child)
    (offers : Finset BareMessage)
    (hOffers : edge.future = FutureSpec.explicit offers) : offers = ∅ := by
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  obtain ⟨childEdge, hChildEdge, rfl⟩ := hEdge
  exact hChild childEdge hChildEdge offers
    (childFutureSpec_explicit index childEdge.future offers hOffers)

/-- The sequence constructor rebuilds every future field, storing a menu only
on the clock edges that end the cycle. -/
theorem sequenceRedirectFutureSpec_explicit
    (label : AutomatonConstructionLabel) (target : TypeAutomatonState)
    (removed offers : Finset BareMessage)
    (hSpec : sequenceRedirectFutureSpec label target removed =
      FutureSpec.explicit offers) : offers = ∅ := by
  by_cases hTock : label.semantic = TypeLabel.tock <;>
    simp [sequenceRedirectFutureSpec, hTock] at hSpec
  exact hSpec.symm

/- Obsolete after the paper update: parallel stores the witnessing child
futures on non-clock edges too. Retained for comparison, not an assumption.
/-- The parallel constructor likewise stores a menu only on clock edges. -/
theorem parallelFutureSpec_explicit
    (label : AutomatonConstructionLabel) (target : TypeAutomatonState)
    (removed offers : Finset BareMessage)
    (hSpec : parallelFutureSpec label target removed =
      FutureSpec.explicit offers) : offers = ∅ := by
  by_cases hTock : label.semantic = TypeLabel.tock <;>
    simp [parallelFutureSpec, hTock] at hSpec
  exact hSpec.symm
-/

/-- The indexed family of branch copies keeps the invariant. -/
theorem indexedFragmentEdges_storedMenusEmpty
    {Key : Type} (automata : List (Key × AutomatonFragment))
    (hAll : ∀ entry ∈ automata, entry.2.StoredMenusEmpty)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ indexedFragmentEdges automata)
    (offers : Finset BareMessage)
    (hOffers : edge.future = FutureSpec.explicit offers) : offers = ∅ := by
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChild⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    exact childPendingEdges_storedMenusEmpty (indexed.2 + 1) indexed.1.2
      (hAll indexed.1 hEntry) edge hChild offers hOffers

/- Obsolete: composed sequence and parallel fields can store nonempty futures.
theorem compileTypeFuel_storedMenusEmpty :
    ∀ (fuel : Nat) (processType : PactType),
      (compileTypeFuel fuel processType).StoredMenusEmpty := by
  intro fuel
  induction fuel with
  | zero => intro processType edge hEdge offers hOffers; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
      intro processType
      cases processType with
      | skip alphabet =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          simp at hOffers
      | message alphabet msg dir =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (hFiring | hWaiting) | hFinal
          · obtain ⟨environment, -, rfl⟩ := hFiring; simp at hOffers
          · obtain ⟨environment, -, rfl⟩ := hWaiting; simp at hOffers
          · obtain ⟨environment, -, rfl⟩ := hFinal; simp at hOffers
      | tock alphabet =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hAction | hFinal
          · obtain ⟨environment, -, rfl⟩ := hAction
            by_cases hClock : environment.clock <;> simp [hClock] at hOffers
            exact hOffers.symm
          · obtain ⟨environment, -, rfl⟩ := hFinal; simp at hOffers
      | progress alphabet pid =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hAction | hFinal
          · obtain ⟨environment, -, rfl⟩ := hAction; simp at hOffers
          · obtain ⟨environment, -, rfl⟩ := hFinal; simp at hOffers
      | var alphabet name =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          simp at hOffers
      | choice alphabet left right =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with (hLeft | hRight) | hSelection
          · exact childPendingEdges_storedMenusEmpty 0 _ (ih left) edge hLeft
              offers hOffers
          · exact childPendingEdges_storedMenusEmpty 1 _ (ih right) edge hRight
              offers hOffers
          · simp only [Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_insert, Finset.mem_singleton] at hSelection
            obtain ⟨environment, -, hCase⟩ := hSelection
            rcases hCase with rfl | rfl <;> simp at hOffers
      | recur alphabet name body =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with hHeader | hBody
          · simp only [Finset.mem_image, Finset.mem_filter] at hHeader
            obtain ⟨environment, -, rfl⟩ := hHeader
            simp at hOffers
          · simp only [Finset.mem_image] at hBody
            obtain ⟨bodyEdge, hBodyEdge, rfl⟩ := hBody
            by_cases hMarker : bodyEdge.label = .variable name
            · simp [hMarker] at hOffers
            · simp only [hMarker, if_neg, not_false_iff] at hOffers
              exact ih body bodyEdge hBodyEdge offers
                (childFutureSpec_explicit 0 bodyEdge.future offers hOffers)
      | fairChoice alphabet bid left right =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with (hLeft | hRight) | hSelection
          · exact childPendingEdges_storedMenusEmpty 0 _ (ih left) edge hLeft
              offers hOffers
          · exact childPendingEdges_storedMenusEmpty 1 _ (ih right) edge hRight
              offers hOffers
          · simp only [Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_insert, Finset.mem_singleton] at hSelection
            obtain ⟨environment, -, hCase⟩ := hSelection
            rcases hCase with rfl | rfl <;> simp at hOffers
      | seq alphabet left right =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with (hLeft | hRight) | hRedirect
          · simp only [sequenceLeftEdges, Finset.mem_image,
              Finset.mem_filter] at hLeft
            obtain ⟨leftEdge, -, rfl⟩ := hLeft
            exact sequenceRedirectFutureSpec_explicit _ _ _ offers hOffers
          · exact childPendingEdges_storedMenusEmpty 1 _ (ih right) edge hRight
              offers hOffers
          · simp only [sequenceRedirectEdges, Finset.mem_image,
              Finset.mem_filter] at hRedirect
            obtain ⟨leftEdge, -, rfl⟩ := hRedirect
            exact sequenceRedirectFutureSpec_explicit _ _ _ offers hOffers
      | par alphabet left right interface =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with
            ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
              hRightSurvivor) | hLeftDone) | hRightDone) | hDone
          · simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hRaw
            obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hRaw
            exact parallelFutureSpec_explicit _ _ _ offers hOffers
          · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hLeftComplete
            obtain ⟨leftState, -, rightEdge, -, survivorEnv, -, rfl⟩ :=
              hLeftComplete
            exact parallelFutureSpec_explicit _ _ _ offers hOffers
          · simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hRightComplete
            obtain ⟨rightState, -, leftEdge, -, survivorEnv, -, rfl⟩ :=
              hRightComplete
            exact parallelFutureSpec_explicit _ _ _ offers hOffers
          · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
              Finset.mem_image] at hLeftSurvivor
            obtain ⟨rightEdge, -, rfl⟩ := hLeftSurvivor
            exact parallelFutureSpec_explicit _ _ _ offers hOffers
          · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
              Finset.mem_image] at hRightSurvivor
            obtain ⟨leftEdge, -, rfl⟩ := hRightSurvivor
            exact parallelFutureSpec_explicit _ _ _ offers hOffers
          · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
              Finset.mem_image] at hLeftDone
            obtain ⟨rightEdge, -, rfl⟩ := hLeftDone
            exact parallelFutureSpec_explicit _ _ _ offers hOffers
          · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
              Finset.mem_image] at hRightDone
            obtain ⟨leftEdge, -, rfl⟩ := hRightDone
            exact parallelFutureSpec_explicit _ _ _ offers hOffers
          · simp only [parallelDoneEdges, Finset.mem_image,
              Finset.mem_filter] at hDone
            obtain ⟨environment, -, rfl⟩ := hDone
            simp at hOffers
            exact hOffers.symm
      | xoffer alphabet elseType branches =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) |
            hElseRoot)
          · exact childPendingEdges_storedMenusEmpty 0 _ (ih elseType) edge
              hElse offers hOffers
          · refine indexedFragmentEdges_storedMenusEmpty _ ?_ edge hIndexed
              offers hOffers
            intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨branch, -, rfl⟩ := hEntry
            exact ih branch.2
          · rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨indexed, -, hNew⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNew
              obtain ⟨environment, -, rfl⟩ := hNew
              simp at hOffers
          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            obtain ⟨environment, -, rfl⟩ := hWait
            simp at hOffers
          · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
            obtain ⟨environment, -, rfl⟩ := hElseRoot
            simp at hOffers
      | offer alphabet elseType branches =>
          intro edge hEdge offers hOffers
          simp only [compileTypeFuel, buildAtomicConjunctiveOfferAutomaton, conjunctiveFiringEdges,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) |
            hElseRoot)
          · exact childPendingEdges_storedMenusEmpty 0 _ (ih elseType) edge
              hElse offers hOffers
          · refine indexedFragmentEdges_storedMenusEmpty _ ?_ edge hIndexed
              offers hOffers
            intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨selected, -, rfl⟩ := hEntry
            exact ih _
          · rw [mem_foldl_union_iff] at hEnabled
            rcases hEnabled with hEmpty | ⟨indexed, -, hNew⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNew
              obtain ⟨environment, -, rfl⟩ := hNew
              simp at hOffers
          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            obtain ⟨environment, -, rfl⟩ := hWait
            simp at hOffers
          · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
            obtain ⟨environment, -, rfl⟩ := hElseRoot
            simp at hOffers


-/

/-- A symbolic continuation always names the edge's own target: the compiler
never points a same-cycle reference at a state the edge does not enter. -/
def AutomatonFragment.FutureTargetsAreEdgeTargets (fragment : AutomatonFragment) :
    Prop :=
  ∀ edge ∈ fragment.edges, ∀ target removed,
    edge.future = FutureSpec.at target removed → target = edge.target

theorem childFutureSpec_at (index : Nat) (spec : FutureSpec)
    (target : TypeAutomatonState) (removed : Finset BareMessage)
    (hSpec : childFutureSpec index spec = FutureSpec.at target removed) :
    ∃ inner, spec = FutureSpec.at inner removed ∧
      target = childState index inner := by
  cases spec with
  | explicit offers => simp [childFutureSpec] at hSpec
  | «at» state rest =>
      simp only [childFutureSpec, FutureSpec.at.injEq] at hSpec
      exact ⟨state, by rw [hSpec.2], hSpec.1.symm⟩
  | atUnion offers state rest => simp [childFutureSpec] at hSpec

theorem childPendingEdges_futureTargets (index : Nat)
    (child : AutomatonFragment) (hChild : child.FutureTargetsAreEdgeTargets)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ childPendingEdges index child)
    (target : TypeAutomatonState) (removed : Finset BareMessage)
    (hFuture : edge.future = FutureSpec.at target removed) :
    target = edge.target := by
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  obtain ⟨childEdge, hChildEdge, rfl⟩ := hEdge
  obtain ⟨inner, hInner, rfl⟩ := childFutureSpec_at index childEdge.future
    target removed hFuture
  simp only [childPendingEdge]
  exact congrArg (childState index)
    (hChild childEdge hChildEdge inner removed hInner)

theorem indexedFragmentEdges_futureTargets
    {Key : Type} (automata : List (Key × AutomatonFragment))
    (hAll : ∀ entry ∈ automata, entry.2.FutureTargetsAreEdgeTargets)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ indexedFragmentEdges automata)
    (target : TypeAutomatonState) (removed : Finset BareMessage)
    (hFuture : edge.future = FutureSpec.at target removed) :
    target = edge.target := by
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChild⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    exact childPendingEdges_futureTargets (indexed.2 + 1) indexed.1.2
      (hAll indexed.1 hEntry) edge hChild target removed hFuture

theorem sequenceRedirectFutureSpec_at
    (label : AutomatonConstructionLabel) (specTarget : TypeAutomatonState)
    (removed : Finset BareMessage) (target : TypeAutomatonState)
    (rest : Finset BareMessage)
    (hSpec : sequenceRedirectFutureSpec label specTarget removed =
      FutureSpec.at target rest) : target = specTarget := by
  by_cases hTock : label.semantic = TypeLabel.tock <;>
    simp [sequenceRedirectFutureSpec, hTock] at hSpec
  exact hSpec.1.symm

/- Obsolete: parallel fields are resolved child fields, while choice and
exclusive-offer fields refer to their source. Menu paths use execution targets.
theorem parallelFutureSpec_at
    (label : AutomatonConstructionLabel) (specTarget : TypeAutomatonState)
    (removed : Finset BareMessage) (target : TypeAutomatonState)
    (rest : Finset BareMessage)
    (hSpec : parallelFutureSpec label specTarget removed =
      FutureSpec.at target rest) : target = specTarget := by
  by_cases hTock : label.semantic = TypeLabel.tock <;>
    simp [parallelFutureSpec, hTock] at hSpec
  exact hSpec.1.symm

theorem compileTypeFuel_futureTargetsAreEdgeTargets :
    ∀ (fuel : Nat) (processType : PactType),
      (compileTypeFuel fuel processType).FutureTargetsAreEdgeTargets := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType edge hEdge target removed hFuture
      simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
      intro processType
      cases processType with
      | skip alphabet =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          simp at hFuture ⊢
          exact hFuture.1.symm
      | message alphabet msg dir =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (hFiring | hWaiting) | hFinal
          · obtain ⟨environment, -, rfl⟩ := hFiring
            simp at hFuture ⊢; exact hFuture.1.symm
          · obtain ⟨environment, -, rfl⟩ := hWaiting
            simp at hFuture ⊢; exact hFuture.1.symm
          · obtain ⟨environment, -, rfl⟩ := hFinal
            simp at hFuture ⊢; exact hFuture.1.symm
      | tock alphabet =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hAction | hFinal
          · obtain ⟨environment, -, rfl⟩ := hAction
            by_cases hClock : environment.clock <;> simp [hClock] at hFuture ⊢
            exact hFuture.1.symm
          · obtain ⟨environment, -, rfl⟩ := hFinal
            simp at hFuture ⊢; exact hFuture.1.symm
      | progress alphabet pid =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hAction | hFinal
          · obtain ⟨environment, -, rfl⟩ := hAction
            simp at hFuture ⊢; exact hFuture.1.symm
          · obtain ⟨environment, -, rfl⟩ := hFinal
            simp at hFuture ⊢; exact hFuture.1.symm
      | var alphabet name =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          simp at hFuture ⊢; exact hFuture.1.symm
      | choice alphabet left right =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with (hLeft | hRight) | hSelection
          · exact childPendingEdges_futureTargets 0 _ (ih left) edge hLeft
              target removed hFuture
          · exact childPendingEdges_futureTargets 1 _ (ih right) edge hRight
              target removed hFuture
          · simp only [Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_insert, Finset.mem_singleton] at hSelection
            obtain ⟨environment, -, hCase⟩ := hSelection
            rcases hCase with rfl | rfl <;>
              (simp at hFuture ⊢; exact hFuture.1.symm)
      | fairChoice alphabet bid left right =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with (hLeft | hRight) | hSelection
          · exact childPendingEdges_futureTargets 0 _ (ih left) edge hLeft
              target removed hFuture
          · exact childPendingEdges_futureTargets 1 _ (ih right) edge hRight
              target removed hFuture
          · simp only [Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_insert, Finset.mem_singleton] at hSelection
            obtain ⟨environment, -, hCase⟩ := hSelection
            rcases hCase with rfl | rfl <;>
              (simp at hFuture ⊢; exact hFuture.1.symm)
      | recur alphabet name body =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with hHeader | hBody
          · simp only [Finset.mem_image, Finset.mem_filter] at hHeader
            obtain ⟨environment, -, rfl⟩ := hHeader
            simp at hFuture ⊢; exact hFuture.1.symm
          · simp only [Finset.mem_image] at hBody
            obtain ⟨bodyEdge, hBodyEdge, rfl⟩ := hBody
            by_cases hMarker : bodyEdge.label = .variable name
            · simp [hMarker] at hFuture ⊢; exact hFuture.1.symm
            · simp only [hMarker, if_neg, not_false_iff] at hFuture ⊢
              obtain ⟨inner, hInner, rfl⟩ :=
                childFutureSpec_at 0 bodyEdge.future target removed hFuture
              exact congrArg (childState 0)
                (ih body bodyEdge hBodyEdge inner removed hInner)
      | seq alphabet left right =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with (hLeft | hRight) | hRedirect
          · simp only [sequenceLeftEdges, Finset.mem_image,
              Finset.mem_filter] at hLeft
            obtain ⟨leftEdge, hLeftMem, rfl⟩ := hLeft
            have hTarget := sequenceRedirectFutureSpec_at _ _ _ target removed
              hFuture
            simp only [sequenceKeptLeftEdge] at hTarget ⊢
            rw [hTarget, sequenceRedirect, if_neg hLeftMem.2.2]
          · exact childPendingEdges_futureTargets 1 _ (ih right) edge hRight
              target removed hFuture
          · simp only [sequenceRedirectEdges, Finset.mem_image,
              Finset.mem_filter] at hRedirect
            obtain ⟨leftEdge, -, rfl⟩ := hRedirect
            exact sequenceRedirectFutureSpec_at _ _ _ target removed hFuture
      | par alphabet left right interface =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with
            ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
              hRightSurvivor) | hLeftDone) | hRightDone) | hDone
          · simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hRaw
            obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hRaw
            exact parallelFutureSpec_at _ _ _ target removed hFuture
          · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hLeftComplete
            obtain ⟨leftState, -, rightEdge, -, survivorEnv, -, rfl⟩ :=
              hLeftComplete
            exact parallelFutureSpec_at _ _ _ target removed hFuture
          · simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hRightComplete
            obtain ⟨rightState, -, leftEdge, -, survivorEnv, -, rfl⟩ :=
              hRightComplete
            exact parallelFutureSpec_at _ _ _ target removed hFuture
          · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
              Finset.mem_image] at hLeftSurvivor
            obtain ⟨rightEdge, -, rfl⟩ := hLeftSurvivor
            exact parallelFutureSpec_at _ _ _ target removed hFuture
          · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
              Finset.mem_image] at hRightSurvivor
            obtain ⟨leftEdge, -, rfl⟩ := hRightSurvivor
            exact parallelFutureSpec_at _ _ _ target removed hFuture
          · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
              Finset.mem_image] at hLeftDone
            obtain ⟨rightEdge, -, rfl⟩ := hLeftDone
            exact parallelFutureSpec_at _ _ _ target removed hFuture
          · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
              Finset.mem_image] at hRightDone
            obtain ⟨leftEdge, -, rfl⟩ := hRightDone
            exact parallelFutureSpec_at _ _ _ target removed hFuture
          · simp only [parallelDoneEdges, Finset.mem_image,
              Finset.mem_filter] at hDone
            obtain ⟨environment, -, rfl⟩ := hDone
            simp at hFuture
      | xoffer alphabet elseType branches =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) |
            hElseRoot)
          · exact childPendingEdges_futureTargets 0 _ (ih elseType) edge
              hElse target removed hFuture
          · refine indexedFragmentEdges_futureTargets _ ?_ edge hIndexed
              target removed hFuture
            intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨branch, -, rfl⟩ := hEntry
            exact ih branch.2
          · rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨indexed, -, hNew⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNew
              obtain ⟨environment, -, rfl⟩ := hNew
              simp at hFuture ⊢; exact hFuture.1.symm
          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            obtain ⟨environment, -, rfl⟩ := hWait
            simp at hFuture ⊢; exact hFuture.1.symm
          · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
            obtain ⟨environment, -, rfl⟩ := hElseRoot
            simp at hFuture ⊢; exact hFuture.1.symm
      | offer alphabet elseType branches =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, buildAtomicConjunctiveOfferAutomaton, conjunctiveFiringEdges,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) |
            hElseRoot)
          · exact childPendingEdges_futureTargets 0 _ (ih elseType) edge
              hElse target removed hFuture
          · refine indexedFragmentEdges_futureTargets _ ?_ edge hIndexed
              target removed hFuture
            intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨selected, -, rfl⟩ := hEntry
            exact ih _
          · rw [mem_foldl_union_iff] at hEnabled
            rcases hEnabled with hEmpty | ⟨indexed, -, hNew⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNew
              obtain ⟨environment, -, rfl⟩ := hNew
              simp at hFuture ⊢; exact hFuture.1.symm
          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            obtain ⟨environment, -, rfl⟩ := hWait
            simp at hFuture ⊢; exact hFuture.1.symm
          · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
            obtain ⟨environment, -, rfl⟩ := hElseRoot
            simp at hFuture ⊢; exact hFuture.1.symm


-/

/-- An accepting state is inert: it publishes no offer, it never leaves the
accepting set, and it carries no unresolved call.  The last conjunct is what
makes a survivor's completion faithful -- a recursion whose body can still
offer has no accepting state at all. -/
def AutomatonFragment.AcceptingInert (fragment : AutomatonFragment) : Prop :=
  ∀ edge ∈ fragment.edges, edge.source ∈ fragment.accepting →
    edge.current = ∅ ∧ edge.target ∈ fragment.accepting ∧
      ∀ name, edge.label ≠ AutomatonConstructionLabel.variable name

theorem childPendingEdges_acceptingInert (index : Nat)
    (child : AutomatonFragment) (hChild : child.AcceptingInert)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ childPendingEdges index child)
    (hSource : edge.source ∈ childAccepting index child) :
    edge.current = ∅ ∧ edge.target ∈ childAccepting index child ∧
      ∀ name, edge.label ≠ AutomatonConstructionLabel.variable name := by
  classical
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  obtain ⟨childEdge, hChildEdge, rfl⟩ := hEdge
  simp only [childPendingEdge, childAccepting, Finset.mem_image] at hSource ⊢
  obtain ⟨accepting, hAccepting, hEq⟩ := hSource
  have hSourceMem : childEdge.source ∈ child.accepting := by
    simp only [childState, TypeAutomatonState.child.injEq] at hEq
    rw [← hEq.2]; exact hAccepting
  obtain ⟨hCurrent, hTarget, hLabel⟩ := hChild childEdge hChildEdge hSourceMem
  exact ⟨hCurrent, ⟨childEdge.target, hTarget, rfl⟩, hLabel⟩

theorem childState_mem_childAccepting_iff (i j : Nat) (f : AutomatonFragment)
    (q : TypeAutomatonState) :
    childState i q ∈ childAccepting j f ↔ i = j ∧ q ∈ f.accepting := by
  classical
  simp only [childAccepting, childState, Finset.mem_image]
  constructor
  · rintro ⟨accepting, hAccepting, hEq⟩
    simp only [TypeAutomatonState.child.injEq] at hEq
    exact ⟨hEq.1.symm, by rw [← hEq.2]; exact hAccepting⟩
  · rintro ⟨rfl, hq⟩
    exact ⟨q, hq, rfl⟩

theorem indexedFragmentEdges_acceptingInert
    {Key : Type} (automata : List (Key × AutomatonFragment))
    (hAll : ∀ entry ∈ automata, entry.2.AcceptingInert)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ indexedFragmentEdges automata)
    (hSource : edge.source ∈ indexedFragmentAccepting automata) :
    edge.current = ∅ ∧ edge.target ∈ indexedFragmentAccepting automata ∧
      ∀ name, edge.label ≠ AutomatonConstructionLabel.variable name := by
  classical
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChild⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    have hAcc : indexedFragmentAccepting automata =
        automata.zipIdx.foldl (fun states indexed =>
          states ∪ childAccepting (indexed.2 + 1) indexed.1.2) ∅ := rfl
    rw [hAcc, mem_foldl_union_iff] at hSource
    rcases hSource with hEmptyAcc | ⟨other, hOther, hOtherAcc⟩
    · simp at hEmptyAcc
    · simp only [childPendingEdges, Finset.mem_image] at hChild
      obtain ⟨childEdge, hChildEdge, rfl⟩ := hChild
      simp only [childPendingEdge] at hOtherAcc ⊢
      rw [childState_mem_childAccepting_iff] at hOtherAcc
      obtain ⟨hIndexEq, hAcceptingMem⟩ := hOtherAcc
      have hIdx : other.2 = indexed.2 := by omega
      have hOtherGet : automata[other.2]? = some other.1 :=
        List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hOther)
      have hIndexedGet : automata[indexed.2]? = some indexed.1 :=
        List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hIndexed)
      have hFst : other.1 = indexed.1 := by
        rw [hIdx] at hOtherGet
        exact Option.some_injective _ (hOtherGet.symm.trans hIndexedGet)
      have hSame : childEdge.source ∈ indexed.1.2.accepting := by
        rw [← hFst]; exact hAcceptingMem
      obtain ⟨hCurrent, hTarget, hLabel⟩ :=
        hAll indexed.1 hEntry childEdge hChildEdge hSame
      refine ⟨hCurrent, ?_, hLabel⟩
      rw [hAcc, mem_foldl_union_iff]
      exact Or.inr ⟨indexed, hIndexed,
        (childState_mem_childAccepting_iff _ _ _ _).mpr ⟨rfl, hTarget⟩⟩

theorem childPendingEdges_source (index : Nat) (child : AutomatonFragment)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ childPendingEdges index child) :
    ∃ q, edge.source = childState index q := by
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  obtain ⟨childEdge, -, rfl⟩ := hEdge
  exact ⟨childEdge.source, rfl⟩

theorem compileTypeFuel_acceptingInert :
    ∀ (fuel : Nat) (processType : PactType),
      (compileTypeFuel fuel processType).AcceptingInert := by
  intro fuel
  induction fuel with
  | zero => intro processType edge hEdge hSource; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
      intro processType
      cases processType with
      | skip alphabet =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          refine ⟨rfl, ?_, by simp⟩
          simp [compileTypeFuel, finishAutomatonFragment]
      | message alphabet msg dir =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_singleton] at hSource
          rcases hEdge with (hFiring | hWaiting) | hFinal
          · obtain ⟨environment, -, rfl⟩ := hFiring; simp at hSource
          · obtain ⟨environment, -, rfl⟩ := hWaiting; simp at hSource
          · obtain ⟨environment, -, rfl⟩ := hFinal
            refine ⟨rfl, ?_, by simp⟩
            simp [compileTypeFuel, finishAutomatonFragment]
      | tock alphabet =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_singleton] at hSource
          rcases hEdge with hAction | hFinal
          · obtain ⟨environment, -, rfl⟩ := hAction
            by_cases hClock : environment.clock <;> simp [hClock] at hSource
          · obtain ⟨environment, -, rfl⟩ := hFinal
            refine ⟨rfl, ?_, by simp⟩
            simp [compileTypeFuel, finishAutomatonFragment]
      | progress alphabet pid =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_singleton] at hSource
          rcases hEdge with hAction | hFinal
          · obtain ⟨environment, -, rfl⟩ := hAction; simp at hSource
          · obtain ⟨environment, -, rfl⟩ := hFinal
            refine ⟨rfl, ?_, by simp⟩
            simp [compileTypeFuel, finishAutomatonFragment]
      | var alphabet name =>
          intro edge hEdge hSource
          simp [compileTypeFuel, finishAutomatonFragment] at hSource
      | choice alphabet left right =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge hSource ⊢
          rcases hEdge with (hLeft | hRight) | hSelection
          · obtain ⟨q, hq⟩ := childPendingEdges_source 0 _ edge hLeft
            have hSrc : edge.source ∈ childAccepting 0
                (compileTypeFuel fuel left) := by
              rcases hSource with h0 | h1
              · exact h0
              · rw [hq, childState_mem_childAccepting_iff] at h1
                exact absurd h1.1 (by decide)
            obtain ⟨hC, hT, hL⟩ := childPendingEdges_acceptingInert 0 _
              (ih left) edge hLeft hSrc
            exact ⟨hC, Or.inl hT, hL⟩
          · obtain ⟨q, hq⟩ := childPendingEdges_source 1 _ edge hRight
            have hSrc : edge.source ∈ childAccepting 1
                (compileTypeFuel fuel right) := by
              rcases hSource with h0 | h1
              · rw [hq, childState_mem_childAccepting_iff] at h0
                exact absurd h0.1 (by decide)
              · exact h1
            obtain ⟨hC, hT, hL⟩ := childPendingEdges_acceptingInert 1 _
              (ih right) edge hRight hSrc
            exact ⟨hC, Or.inr hT, hL⟩
          · exfalso
            simp only [Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_insert, Finset.mem_singleton] at hSelection
            obtain ⟨environment, -, hCase⟩ := hSelection
            rcases hCase with rfl | rfl <;>
              (rcases hSource with h | h <;>
                simp [childAccepting, childState] at h)
      | fairChoice alphabet bid left right =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge hSource ⊢
          rcases hEdge with (hLeft | hRight) | hSelection
          · obtain ⟨q, hq⟩ := childPendingEdges_source 0 _ edge hLeft
            have hSrc : edge.source ∈ childAccepting 0
                (compileTypeFuel fuel left) := by
              rcases hSource with h0 | h1
              · exact h0
              · rw [hq, childState_mem_childAccepting_iff] at h1
                exact absurd h1.1 (by decide)
            obtain ⟨hC, hT, hL⟩ := childPendingEdges_acceptingInert 0 _
              (ih left) edge hLeft hSrc
            exact ⟨hC, Or.inl hT, hL⟩
          · obtain ⟨q, hq⟩ := childPendingEdges_source 1 _ edge hRight
            have hSrc : edge.source ∈ childAccepting 1
                (compileTypeFuel fuel right) := by
              rcases hSource with h0 | h1
              · rw [hq, childState_mem_childAccepting_iff] at h0
                exact absurd h0.1 (by decide)
              · exact h1
            obtain ⟨hC, hT, hL⟩ := childPendingEdges_acceptingInert 1 _
              (ih right) edge hRight hSrc
            exact ⟨hC, Or.inr hT, hL⟩
          · exfalso
            simp only [Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_insert, Finset.mem_singleton] at hSelection
            obtain ⟨environment, -, hCase⟩ := hSelection
            rcases hCase with rfl | rfl <;>
              (rcases hSource with h | h <;>
                simp [childAccepting, childState] at h)
      | recur alphabet name body =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge hSource ⊢
          rcases hEdge with hHeader | hBody
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hHeader
            obtain ⟨environment, -, rfl⟩ := hHeader
            simp [childAccepting, childState] at hSource
          · simp only [Finset.mem_image] at hBody
            obtain ⟨bodyEdge, hBodyEdge, rfl⟩ := hBody
            by_cases hMarker : bodyEdge.label = .variable name
            · exfalso
              simp only [hMarker, if_pos] at hSource
              rw [childState_mem_childAccepting_iff] at hSource
              exact (ih body bodyEdge hBodyEdge hSource.2).2.2 name hMarker
            · simp only [hMarker, if_neg, not_false_iff] at hSource ⊢
              rw [childState_mem_childAccepting_iff] at hSource
              obtain ⟨hC, hT, hL⟩ := ih body bodyEdge hBodyEdge hSource.2
              exact ⟨hC, (childState_mem_childAccepting_iff _ _ _ _).mpr
                ⟨rfl, hT⟩, hL⟩
      | seq alphabet left right =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge hSource ⊢
          rcases hEdge with (hLeft | hRight) | hRedirect
          · exfalso
            simp only [sequenceLeftEdges, Finset.mem_image,
              Finset.mem_filter] at hLeft
            obtain ⟨leftEdge, -, rfl⟩ := hLeft
            simp only [sequenceKeptLeftEdge,
              childState_mem_childAccepting_iff] at hSource
            exact absurd hSource.1 (by decide)
          · exact childPendingEdges_acceptingInert 1 _ (ih right) edge hRight
              hSource
          · exfalso
            simp only [sequenceRedirectEdges, Finset.mem_image,
              Finset.mem_filter] at hRedirect
            obtain ⟨leftEdge, -, rfl⟩ := hRedirect
            simp only [sequenceRedirectEdge,
              childState_mem_childAccepting_iff] at hSource
            exact absurd hSource.1 (by decide)
      | par alphabet left right interface =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_union,
            Finset.mem_singleton] at hEdge hSource ⊢
          rcases hEdge with
            ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
              hRightSurvivor) | hLeftDone) | hRightDone) | hDone
          · exfalso
            simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hRaw
            obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hRaw
            simp at hSource
          · exfalso
            simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hLeftComplete
            obtain ⟨leftState, -, rightEdge, -, survivorEnv, -, rfl⟩ :=
              hLeftComplete
            simp at hSource
          · exfalso
            simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hRightComplete
            obtain ⟨rightState, -, leftEdge, -, survivorEnv, -, rfl⟩ :=
              hRightComplete
            simp at hSource
          · exfalso
            simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
              Finset.mem_image] at hLeftSurvivor
            obtain ⟨rightEdge, -, rfl⟩ := hLeftSurvivor
            simp at hSource
          · exfalso
            simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
              Finset.mem_image] at hRightSurvivor
            obtain ⟨leftEdge, -, rfl⟩ := hRightSurvivor
            simp at hSource
          · exfalso
            simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
              Finset.mem_image] at hLeftDone
            obtain ⟨rightEdge, -, rfl⟩ := hLeftDone
            simp at hSource
          · exfalso
            simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
              Finset.mem_image] at hRightDone
            obtain ⟨leftEdge, -, rfl⟩ := hRightDone
            simp at hSource
          · simp only [parallelDoneEdges, Finset.mem_image,
              Finset.mem_filter] at hDone
            obtain ⟨environment, -, rfl⟩ := hDone
            exact ⟨rfl, rfl, by simp⟩
      | xoffer alphabet elseType branches =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge hSource ⊢
          rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) |
            hElseRoot)
          · obtain ⟨q, hq⟩ := childPendingEdges_source 0 _ edge hElse
            have hSrc : edge.source ∈ childAccepting 0
                (compileTypeFuel fuel elseType) := by
              rcases hSource with h0 | h1
              · exact h0
              · exfalso
                rw [hq] at h1
                rw [indexedFragmentAccepting, mem_foldl_union_iff] at h1
                rcases h1 with hE | ⟨indexed, -, hMem⟩
                · simp at hE
                · rw [childState_mem_childAccepting_iff] at hMem
                  omega
            obtain ⟨hC, hT, hL⟩ := childPendingEdges_acceptingInert 0 _
              (ih elseType) edge hElse hSrc
            exact ⟨hC, Or.inl hT, hL⟩
          · have hSrc : edge.source ∈ indexedFragmentAccepting
                (branches.map fun branch =>
                  (branch.1, compileTypeFuel fuel branch.2)) := by
              rcases hSource with h0 | h1
              · exfalso
                rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
                rcases hIndexed with hE | ⟨indexed, -, hMem⟩
                · simp at hE
                · obtain ⟨q, hq⟩ := childPendingEdges_source (indexed.2 + 1) _
                    edge hMem
                  rw [hq, childState_mem_childAccepting_iff] at h0
                  omega
              · exact h1
            refine ⟨?_, ?_, ?_⟩ <;>
              [skip; skip; skip]
            all_goals (
              have hAll : ∀ entry ∈ (branches.map fun branch =>
                  (branch.1, compileTypeFuel fuel branch.2)),
                  entry.2.AcceptingInert := by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨branch, -, rfl⟩ := hEntry
                exact ih branch.2
              have hRes := indexedFragmentEdges_acceptingInert _ hAll edge
                hIndexed hSrc)
            · exact hRes.1
            · exact Or.inr hRes.2.1
            · exact hRes.2.2
          · exfalso
            rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hE | ⟨indexed, -, hNew⟩
            · simp at hE
            · simp only [Finset.mem_image, Finset.mem_filter] at hNew
              obtain ⟨environment, -, rfl⟩ := hNew
              rcases hSource with h | h
              · simp [childAccepting, childState] at h
              · rw [indexedFragmentAccepting, mem_foldl_union_iff] at h
                rcases h with hE | ⟨other, -, hMem⟩
                · simp at hE
                · simp [childAccepting, childState] at hMem
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hWait
            obtain ⟨environment, -, rfl⟩ := hWait
            rcases hSource with h | h
            · simp [childAccepting, childState] at h
            · rw [indexedFragmentAccepting, mem_foldl_union_iff] at h
              rcases h with hE | ⟨other, -, hMem⟩
              · simp at hE
              · simp [childAccepting, childState] at hMem
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
            obtain ⟨environment, -, rfl⟩ := hElseRoot
            rcases hSource with h | h
            · simp [childAccepting, childState] at h
            · rw [indexedFragmentAccepting, mem_foldl_union_iff] at h
              rcases h with hE | ⟨other, -, hMem⟩
              · simp at hE
              · simp [childAccepting, childState] at hMem
      | offer alphabet elseType branches =>
          intro edge hEdge hSource
          simp only [compileTypeFuel, buildAtomicConjunctiveOfferAutomaton, conjunctiveFiringEdges,
            finishAutomatonFragment, Finset.mem_union] at hEdge hSource ⊢
          rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) |
            hElseRoot)
          · obtain ⟨q, hq⟩ := childPendingEdges_source 0 _ edge hElse
            have hSrc : edge.source ∈ childAccepting 0
                (compileTypeFuel fuel elseType) := by
              rcases hSource with h0 | h1
              · exact h0
              · exfalso
                rw [hq] at h1
                rw [indexedFragmentAccepting, mem_foldl_union_iff] at h1
                rcases h1 with hE | ⟨indexed, -, hMem⟩
                · simp at hE
                · rw [childState_mem_childAccepting_iff] at hMem
                  omega
            obtain ⟨hC, hT, hL⟩ := childPendingEdges_acceptingInert 0 _
              (ih elseType) edge hElse hSrc
            exact ⟨hC, Or.inl hT, hL⟩
          · have hSrc : edge.source ∈ indexedFragmentAccepting
                ((conjunctiveSelections branches.length).toList.map fun selected =>
                  (selected, compileTypeFuel fuel
                    (parallelTypeBranchesFiring alphabet selected branches))) := by
              rcases hSource with h0 | h1
              · exfalso
                rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
                rcases hIndexed with hE | ⟨indexed, -, hMem⟩
                · simp at hE
                · obtain ⟨q, hq⟩ := childPendingEdges_source (indexed.2 + 1) _
                    edge hMem
                  rw [hq, childState_mem_childAccepting_iff] at h0
                  omega
              · exact h1
            refine ⟨?_, ?_, ?_⟩ <;>
              [skip; skip; skip]
            all_goals (
              have hAll : ∀ entry ∈ ((conjunctiveSelections branches.length).toList.map fun selected =>
                  (selected, compileTypeFuel fuel
                    (parallelTypeBranchesFiring alphabet selected branches))),
                  entry.2.AcceptingInert := by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨selected, -, rfl⟩ := hEntry
                exact ih _
              have hRes := indexedFragmentEdges_acceptingInert _ hAll edge
                hIndexed hSrc)
            · exact hRes.1
            · exact Or.inr hRes.2.1
            · exact hRes.2.2
          · exfalso
            rw [mem_foldl_union_iff] at hEnabled
            rcases hEnabled with hE | ⟨indexed, -, hNew⟩
            · simp at hE
            · simp only [Finset.mem_image, Finset.mem_filter] at hNew
              obtain ⟨environment, -, rfl⟩ := hNew
              rcases hSource with h | h
              · simp [childAccepting, childState] at h
              · rw [indexedFragmentAccepting, mem_foldl_union_iff] at h
                rcases h with hE | ⟨other, -, hMem⟩
                · simp at hE
                · simp [childAccepting, childState] at hMem
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hWait
            obtain ⟨environment, -, rfl⟩ := hWait
            rcases hSource with h | h
            · simp [childAccepting, childState] at h
            · rw [indexedFragmentAccepting, mem_foldl_union_iff] at h
              rcases h with hE | ⟨other, -, hMem⟩
              · simp at hE
              · simp [childAccepting, childState] at hMem
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
            obtain ⟨environment, -, rfl⟩ := hElseRoot
            rcases hSource with h | h
            · simp [childAccepting, childState] at h
            · rw [indexedFragmentAccepting, mem_foldl_union_iff] at h
              rcases h with hE | ⟨other, -, hMem⟩
              · simp at hE
              · simp [childAccepting, childState] at hMem


/-- No accepting state carries a product term: a parallel accepts only at its
dedicated done state, and every tag above it forwards the query to a child. -/
theorem compileTypeFuel_accepting_stateProductInfoFuel_none :
    ∀ (fuel : Nat) (processType : PactType) (state : TypeAutomatonState),
      state ∈ (compileTypeFuel fuel processType).accepting →
      stateProductInfoFuel fuel processType state = none := by
  intro fuel
  induction fuel with
  | zero => intro processType state hState; simp [stateProductInfoFuel]
  | succ fuel ih =>
      intro processType state hState
      cases processType with
      | skip alphabet => cases state <;> simp [stateProductInfoFuel]
      | message alphabet msg dir => cases state <;> simp [stateProductInfoFuel]
      | tock alphabet => cases state <;> simp [stateProductInfoFuel]
      | progress alphabet pid => cases state <;> simp [stateProductInfoFuel]
      | var alphabet name => cases state <;> simp [stateProductInfoFuel]
      | choice alphabet left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hState
          rcases hState with h0 | h1
          · simp only [childAccepting, Finset.mem_image] at h0
            obtain ⟨q, hq, rfl⟩ := h0
            simp only [childState, stateProductInfoFuel]
            exact ih left q hq
          · simp only [childAccepting, Finset.mem_image] at h1
            obtain ⟨q, hq, rfl⟩ := h1
            simp only [childState, stateProductInfoFuel]
            exact ih right q hq
      | fairChoice alphabet bid left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hState
          rcases hState with h0 | h1
          · simp only [childAccepting, Finset.mem_image] at h0
            obtain ⟨q, hq, rfl⟩ := h0
            simp only [childState, stateProductInfoFuel]
            exact ih left q hq
          · simp only [childAccepting, Finset.mem_image] at h1
            obtain ⟨q, hq, rfl⟩ := h1
            simp only [childState, stateProductInfoFuel]
            exact ih right q hq
      | recur alphabet name body =>
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, childAccepting,
            Finset.mem_image] at hState
          obtain ⟨q, hq, rfl⟩ := hState
          simp only [childState, stateProductInfoFuel]
          exact ih body q hq
      | seq alphabet left right =>
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childAccepting,
            Finset.mem_image] at hState
          obtain ⟨q, hq, rfl⟩ := hState
          simp only [childState, stateProductInfoFuel]
          exact ih right q hq
      | par alphabet left right interface =>
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_singleton] at hState
          subst hState
          simp [stateProductInfoFuel]
      | xoffer alphabet elseType branches =>
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hState
          rcases hState with hElse | hIndexed
          · simp only [childAccepting, Finset.mem_image] at hElse
            obtain ⟨q, hq, rfl⟩ := hElse
            simp only [childState, stateProductInfoFuel]
            exact ih elseType q hq
          · rw [indexedFragmentAccepting, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hMem, hAcc⟩
            · simp at hEmpty
            · simp only [childAccepting, Finset.mem_image] at hAcc
              obtain ⟨q, hq, rfl⟩ := hAcc
              have hGet : (branches.map fun branch =>
                  (branch.1, compileTypeFuel fuel branch.2))[indexed.2]? =
                  some indexed.1 :=
                List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hMem)
              rw [List.getElem?_map] at hGet
              obtain ⟨branch, hBranch, hEq⟩ := Option.map_eq_some_iff.mp hGet
              simp only [childState, stateProductInfoFuel, hBranch]
              rw [← hEq] at hq
              exact ih branch.2 q hq
      | offer alphabet elseType branches =>
          simp only [compileTypeFuel, buildAtomicConjunctiveOfferAutomaton, conjunctiveFiringEdges,
            finishAutomatonFragment, Finset.mem_union] at hState
          rcases hState with hElse | hIndexed
          · simp only [childAccepting, Finset.mem_image] at hElse
            obtain ⟨q, hq, rfl⟩ := hElse
            simp only [childState, stateProductInfoFuel]
            exact ih elseType q hq
          · rw [indexedFragmentAccepting, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hMem, hAcc⟩
            · simp at hEmpty
            · simp only [childAccepting, Finset.mem_image] at hAcc
              obtain ⟨q, hq, rfl⟩ := hAcc
              have hGet : ((conjunctiveSelections branches.length).toList.map fun selected =>
                  (selected, compileTypeFuel fuel
                    (parallelTypeBranchesFiring alphabet selected
                      branches)))[indexed.2]? = some indexed.1 :=
                List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hMem)
              rw [List.getElem?_map] at hGet
              obtain ⟨selected, hSelected, hEq⟩ := Option.map_eq_some_iff.mp hGet
              simp only [childState, stateProductInfoFuel, hSelected]
              rw [← hEq] at hq
              exact ih _ q hq


/-- Only an accepting state stores a menu on a non-clock edge.  The idle
self-loops of a completed parallel are the sole such family, and every tag
above them keeps the source inside the accepting set. -/
def AutomatonFragment.ExplicitOnlyAtAccepting (fragment : AutomatonFragment) :
    Prop :=
  ∀ edge ∈ fragment.edges, edge.label.semantic ≠ TypeLabel.tock →
    ∀ offers, edge.future = FutureSpec.explicit offers →
      edge.source ∈ fragment.accepting

theorem childPendingEdges_explicitOnlyAtAccepting (index : Nat)
    (child : AutomatonFragment) (hChild : child.ExplicitOnlyAtAccepting)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ childPendingEdges index child)
    (hTock : edge.label.semantic ≠ TypeLabel.tock)
    (offers : Finset BareMessage)
    (hFuture : edge.future = FutureSpec.explicit offers) :
    edge.source ∈ childAccepting index child := by
  classical
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  obtain ⟨childEdge, hChildEdge, rfl⟩ := hEdge
  simp only [childPendingEdge] at hTock hFuture ⊢
  exact (childState_mem_childAccepting_iff _ _ _ _).mpr
    ⟨rfl, hChild childEdge hChildEdge hTock offers
      (childFutureSpec_explicit index childEdge.future offers hFuture)⟩

theorem indexedFragmentEdges_explicitOnlyAtAccepting
    {Key : Type} (automata : List (Key × AutomatonFragment))
    (hAll : ∀ entry ∈ automata, entry.2.ExplicitOnlyAtAccepting)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ indexedFragmentEdges automata)
    (hTock : edge.label.semantic ≠ TypeLabel.tock)
    (offers : Finset BareMessage)
    (hFuture : edge.future = FutureSpec.explicit offers) :
    edge.source ∈ indexedFragmentAccepting automata := by
  classical
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChild⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    have hAcc : indexedFragmentAccepting automata =
        automata.zipIdx.foldl (fun states indexed =>
          states ∪ childAccepting (indexed.2 + 1) indexed.1.2) ∅ := rfl
    rw [hAcc, mem_foldl_union_iff]
    exact Or.inr ⟨indexed, hIndexed,
      childPendingEdges_explicitOnlyAtAccepting (indexed.2 + 1) indexed.1.2
        (hAll indexed.1 hEntry) edge hChild hTock offers hFuture⟩

/- Obsolete: sequence and parallel store component fields at live states too.
theorem compileTypeFuel_explicitOnlyAtAccepting :
    ∀ (fuel : Nat) (processType : PactType),
      (compileTypeFuel fuel processType).ExplicitOnlyAtAccepting := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType edge hEdge hTock offers hFuture
      simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
      intro processType
      cases processType with
      | skip alphabet =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          simp at hFuture
      | message alphabet msg dir =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (h | h) | h <;>
            (obtain ⟨environment, -, rfl⟩ := h; simp at hFuture)
      | tock alphabet =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hAction | hFinal
          · obtain ⟨environment, -, rfl⟩ := hAction
            by_cases hClock : environment.clock
            · exact absurd (by simp [hClock, AutomatonConstructionLabel.semantic])
                hTock
            · simp [hClock] at hFuture
          · obtain ⟨environment, -, rfl⟩ := hFinal
            simp at hFuture
      | progress alphabet pid =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with h | h <;>
            (obtain ⟨environment, -, rfl⟩ := h; simp at hFuture)
      | var alphabet name =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          simp at hFuture
      | choice alphabet left right =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge ⊢
          rcases hEdge with (hLeft | hRight) | hSelection
          · exact Or.inl (childPendingEdges_explicitOnlyAtAccepting 0 _
              (ih left) edge hLeft hTock offers hFuture)
          · exact Or.inr (childPendingEdges_explicitOnlyAtAccepting 1 _
              (ih right) edge hRight hTock offers hFuture)
          · exfalso
            simp only [Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_insert, Finset.mem_singleton] at hSelection
            obtain ⟨environment, -, hCase⟩ := hSelection
            rcases hCase with rfl | rfl <;> simp at hFuture
      | fairChoice alphabet bid left right =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge ⊢
          rcases hEdge with (hLeft | hRight) | hSelection
          · exact Or.inl (childPendingEdges_explicitOnlyAtAccepting 0 _
              (ih left) edge hLeft hTock offers hFuture)
          · exact Or.inr (childPendingEdges_explicitOnlyAtAccepting 1 _
              (ih right) edge hRight hTock offers hFuture)
          · exfalso
            simp only [Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_insert, Finset.mem_singleton] at hSelection
            obtain ⟨environment, -, hCase⟩ := hSelection
            rcases hCase with rfl | rfl <;> simp at hFuture
      | recur alphabet name body =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge ⊢
          rcases hEdge with hHeader | hBody
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hHeader
            obtain ⟨environment, -, rfl⟩ := hHeader
            simp at hFuture
          · simp only [Finset.mem_image] at hBody
            obtain ⟨bodyEdge, hBodyEdge, rfl⟩ := hBody
            by_cases hMarker : bodyEdge.label = .variable name
            · exfalso; simp [hMarker] at hFuture
            · simp only [hMarker, if_neg, not_false_iff] at hTock hFuture ⊢
              exact (childState_mem_childAccepting_iff _ _ _ _).mpr
                ⟨rfl, ih body bodyEdge hBodyEdge hTock offers
                  (childFutureSpec_explicit 0 bodyEdge.future offers hFuture)⟩
      | seq alphabet left right =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge ⊢
          rcases hEdge with (hLeft | hRight) | hRedirect
          · exfalso
            simp only [sequenceLeftEdges, Finset.mem_image,
              Finset.mem_filter] at hLeft
            obtain ⟨leftEdge, -, rfl⟩ := hLeft
            simp only [sequenceKeptLeftEdge] at hTock hFuture
            by_cases hT : leftEdge.label.semantic = TypeLabel.tock <;>
              simp [sequenceRedirectFutureSpec, hT] at hTock hFuture
          · exact childPendingEdges_explicitOnlyAtAccepting 1 _ (ih right)
              edge hRight hTock offers hFuture
          · exfalso
            simp only [sequenceRedirectEdges, Finset.mem_image,
              Finset.mem_filter] at hRedirect
            obtain ⟨leftEdge, -, rfl⟩ := hRedirect
            simp only [sequenceRedirectEdge] at hTock hFuture
            by_cases hT : leftEdge.label.semantic = TypeLabel.tock <;>
              simp [sequenceRedirectFutureSpec, hT] at hTock hFuture
      | par alphabet left right interface =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_union,
            Finset.mem_singleton] at hEdge ⊢
          rcases hEdge with
            ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
              hRightSurvivor) | hLeftDone) | hRightDone) | hDone
          · exfalso
            simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hRaw
            obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hRaw
            exact absurd (parallelFutureSpec_explicit _ _ _ offers hFuture)
              (by
                by_cases hT : (AutomatonConstructionLabel.combine interface
                  leftEdge.label rightEdge.label).semantic = TypeLabel.tock
                · exact absurd hT hTock
                · simp [parallelFutureSpec, hT] at hFuture)
          · exfalso
            simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hLeftComplete
            obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hLeftComplete
            simp only at hTock hFuture
            by_cases hT : (AutomatonConstructionLabel.combine interface
              leftEdge.label rightEdge.label).semantic = TypeLabel.tock <;>
              simp [parallelFutureSpec, hT] at hTock hFuture
          · exfalso
            simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image] at hRightComplete
            obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hRightComplete
            simp only at hTock hFuture
            by_cases hT : (AutomatonConstructionLabel.combine interface
              leftEdge.label rightEdge.label).semantic = TypeLabel.tock <;>
              simp [parallelFutureSpec, hT] at hTock hFuture
          · exfalso
            simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
              Finset.mem_image] at hLeftSurvivor
            obtain ⟨rightEdge, -, rfl⟩ := hLeftSurvivor
            simp only at hTock hFuture
            by_cases hT : rightEdge.label.semantic = TypeLabel.tock <;>
              simp [parallelFutureSpec, hT] at hTock hFuture
          · exfalso
            simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
              Finset.mem_image] at hRightSurvivor
            obtain ⟨leftEdge, -, rfl⟩ := hRightSurvivor
            simp only at hTock hFuture
            by_cases hT : leftEdge.label.semantic = TypeLabel.tock <;>
              simp [parallelFutureSpec, hT] at hTock hFuture
          · exfalso
            simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
              Finset.mem_image] at hLeftDone
            obtain ⟨rightEdge, -, rfl⟩ := hLeftDone
            simp only at hTock hFuture
            by_cases hT : rightEdge.label.semantic = TypeLabel.tock <;>
              simp [parallelFutureSpec, hT] at hTock hFuture
          · exfalso
            simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
              Finset.mem_image] at hRightDone
            obtain ⟨leftEdge, -, rfl⟩ := hRightDone
            simp only at hTock hFuture
            by_cases hT : leftEdge.label.semantic = TypeLabel.tock <;>
              simp [parallelFutureSpec, hT] at hTock hFuture
          · simp only [parallelDoneEdges, Finset.mem_image,
              Finset.mem_filter] at hDone
            obtain ⟨environment, -, rfl⟩ := hDone
            rfl
      | xoffer alphabet elseType branches =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge ⊢
          rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) |
            hElseRoot)
          · exact Or.inl (childPendingEdges_explicitOnlyAtAccepting 0 _
              (ih elseType) edge hElse hTock offers hFuture)
          · refine Or.inr (indexedFragmentEdges_explicitOnlyAtAccepting _ ?_
              edge hIndexed hTock offers hFuture)
            intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨branch, -, rfl⟩ := hEntry
            exact ih branch.2
          · exfalso
            rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hE | ⟨indexed, -, hNew⟩
            · simp at hE
            · simp only [Finset.mem_image, Finset.mem_filter] at hNew
              obtain ⟨environment, -, rfl⟩ := hNew
              simp at hFuture
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hWait
            obtain ⟨environment, -, rfl⟩ := hWait
            simp at hFuture
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
            obtain ⟨environment, -, rfl⟩ := hElseRoot
            simp at hFuture
      | offer alphabet elseType branches =>
          intro edge hEdge hTock offers hFuture
          simp only [compileTypeFuel, buildAtomicConjunctiveOfferAutomaton, conjunctiveFiringEdges,
            finishAutomatonFragment, Finset.mem_union] at hEdge ⊢
          rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) |
            hElseRoot)
          · exact Or.inl (childPendingEdges_explicitOnlyAtAccepting 0 _
              (ih elseType) edge hElse hTock offers hFuture)
          · refine Or.inr (indexedFragmentEdges_explicitOnlyAtAccepting _ ?_
              edge hIndexed hTock offers hFuture)
            intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨selected, -, rfl⟩ := hEntry
            exact ih _
          · exfalso
            rw [mem_foldl_union_iff] at hEnabled
            rcases hEnabled with hE | ⟨indexed, -, hNew⟩
            · simp at hE
            · simp only [Finset.mem_image, Finset.mem_filter] at hNew
              obtain ⟨environment, -, rfl⟩ := hNew
              simp at hFuture
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hWait
            obtain ⟨environment, -, rfl⟩ := hWait
            simp at hFuture
          · exfalso
            simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
            obtain ⟨environment, -, rfl⟩ := hElseRoot
            simp at hFuture

-/

end

end Pact
