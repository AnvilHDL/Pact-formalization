import Anvilpp.PactTypes.NewCorrespondence.Helpers.EnvironmentAndAlphabet

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

theorem compileTypeFuel_futureTargetsInStates (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      (compileTypeFuel signature fuel processType).FutureTargetsInStates := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image] at hEdge
          rcases hEdge with (⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩) |
            ⟨environment, _, rfl⟩ <;> simp at hFuture
      | progress pid =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩ <;>
            simp at hFuture
      | tock =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩
          · split at hFuture <;> simp at hFuture
          · simp at hFuture
      | skip =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image]
            at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp at hFuture
      | var name =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image]
            at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp at hFuture
      | recur name body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          exact buildRecursionAutomaton_futureTargetsInStates signature name
            (compileTypeFuel signature fuel body) (ih body hBody)
            (compileTypeFuel_initial_mem signature fuel body hBody)
      | choice left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) TypeLabel.silent
            TypeLabel.silent (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | fairChoice bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          exact buildSequenceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) (ih left hLeft)
            (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | par left right interface =>
          exact buildParallelAutomaton_futureTargetsInStates signature interface
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
      | xoffer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hBranches : ∀ entry ∈ branches,
              TypeCompilationFuelSufficient entry.2 fuel := by
            intro entry hEntry
            have hBound := typeCompilationFuel_le_typeBranchCompilationFuel
              branches entry hEntry
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            simp only [TypeCompilationFuelSufficient]
            omega
          have hResult := buildExclusiveOfferAutomaton_futureTargetsInStates
            signature branches (compileTypeFuel signature fuel elseType)
            (branches.map fun branch =>
              (branch.1, compileTypeFuel signature fuel branch.2))
            (ih elseType hElse)
            (by
              intro entry hEntry
              simp only [List.mem_map] at hEntry
              obtain ⟨original, hOriginal, rfl⟩ := hEntry
              exact ih original.2 (hBranches original hOriginal))
            (compileTypeFuel_initial_mem signature fuel elseType hElse)
            (by
              intro entry hEntry
              simp only [List.mem_map] at hEntry
              obtain ⟨original, hOriginal, rfl⟩ := hEntry
              exact compileTypeFuel_initial_mem signature fuel original.2
                (hBranches original hOriginal))
          simpa [compileTypeFuel] using hResult
      | offer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hSelected : ∀ selected ∈ branches,
              TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting selected branches) fuel := by
            intro selected hSelected
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hResult :=
            buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates
              signature branches (compileTypeFuel signature fuel elseType)
              (branches.map fun selected =>
                (selected.1, compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting selected branches)))
              (ih elseType hElse)
              (by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨original, hOriginal, rfl⟩ := hEntry
                exact ih (parallelTypeBranchesSelecting original branches)
                  (hSelected original hOriginal))
              (compileTypeFuel_initial_mem signature fuel elseType hElse)
              (by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨original, hOriginal, rfl⟩ := hEntry
                exact compileTypeFuel_initial_mem signature fuel
                  (parallelTypeBranchesSelecting original branches)
                  (hSelected original hOriginal))
          simpa [compileTypeFuel] using hResult

/-- Proves every sufficiently fuelled fragment's pending automaton is closed under its own future references. -/
theorem compileTypeFuel_referencesClosed (signature : TypeAlphabet)
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    ({ states := (compileTypeFuel signature fuel processType).states
       edges := (compileTypeFuel signature fuel processType).edges } :
      PendingAutomaton).ReferencesClosed :=
  PendingAutomaton.referencesClosed_of_futureTargetsInStates
    (compileTypeFuel signature fuel processType)
    (compileTypeFuel_futureTargetsInStates signature fuel processType hFuel)

private theorem stateProductInfoFuel_succ_stable :
    ∀ fuel processType state,
      typeCompilationFuel processType ≤ fuel →
      stateProductInfoFuel (fuel + 1) processType state =
        stateProductInfoFuel fuel processType state := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType state hFuel
      have hPositive := typeCompilationFuel_positive processType
      omega
  | succ fuel ih =>
      intro processType state hFuel
      cases processType with
      | message msg dir => cases state <;> rfl
      | progress pid => cases state <;> rfl
      | tock => cases state <;> rfl
      | skip => cases state <;> rfl
      | var name => cases state <;> rfl
      | recur name body =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ index =>
                  cases index <;> rfl
          | _ => rfl
      | choice left right =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ index =>
                  cases index with
                  | zero =>
                      simp only [stateProductInfoFuel]
                      apply ih
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
                  | succ index => rfl
          | _ => rfl
      | fairChoice bid left right =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ index =>
                  cases index with
                  | zero =>
                      simp only [stateProductInfoFuel]
                      apply ih
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
                  | succ index => rfl
          | _ => rfl
      | seq left right =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ index =>
                  cases index with
                  | zero =>
                      simp only [stateProductInfoFuel]
                      apply ih
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
                  | succ index => rfl
          | _ => rfl
      | par left right interface =>
          cases state <;> rfl
      | xoffer elseType branches =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ i =>
                  simp only [stateProductInfoFuel]
                  cases hBranch : branches[i]? with
                  | none => rfl
                  | some branch =>
                      rcases branch with ⟨action, branchType⟩
                      apply ih
                      have hMem : (action, branchType) ∈ branches :=
                        List.mem_iff_getElem?.mpr ⟨i, hBranch⟩
                      have hBranchFuel :=
                        typeCompilationFuel_le_typeBranchCompilationFuel
                          branches (action, branchType) hMem
                      have hBranchFuel' :
                          typeCompilationFuel branchType ≤
                            typeBranchCompilationFuel branches := by
                        simpa using hBranchFuel
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
          | _ => rfl
      | offer elseType branches =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ i =>
                  simp only [stateProductInfoFuel]
                  cases hSelected : branches[i]? with
                  | none => rfl
                  | some selected =>
                      apply ih
                      rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
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
        stateProductInfoFuel_succ_stable (fuel + extra) processType state
          (by omega),
        ih]

/-- States that `stateProductInfoFuel` stabilizes once its fuel is sufficient, mirroring `compileTypeFuel_eq_of_sufficient`. -/
theorem stateProductInfoFuel_eq_of_sufficient
    (processType : PactType) (state : TypeAutomatonState)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    stateProductInfoFuel leftFuel processType state =
      stateProductInfoFuel rightFuel processType state := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (stateProductInfoFuel_add_stable processType state leftFuel extra
      hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact stateProductInfoFuel_add_stable processType state rightFuel extra
      hRight

theorem stateProductInfoFuel_component_fuel_lt :
    ∀ fuel processType state interface left right q1 q2,
      TypeCompilationFuelSufficient processType fuel →
      stateProductInfoFuel fuel processType state =
        some (interface, left, right, q1, q2) →
      typeCompilationFuel left < fuel ∧
        typeCompilationFuel right < fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType state interface left right q1 q2 hFuel _hInfo
      have hPositive := typeCompilationFuel_positive processType
      exact (by
        simp [TypeCompilationFuelSufficient] at hFuel
        omega)
  | succ fuel ih =>
      intro processType state interface componentLeft componentRight q1 q2
        hFuel hInfo
      cases processType with
      | message msg dir => cases state <;> simp [stateProductInfoFuel] at hInfo
      | progress pid => cases state <;> simp [stateProductInfoFuel] at hInfo
      | tock => cases state <;> simp [stateProductInfoFuel] at hInfo
      | skip => cases state <;> simp [stateProductInfoFuel] at hInfo
      | var name => cases state <;> simp [stateProductInfoFuel] at hInfo
      | recur name body =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih body state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ index =>
                  cases index <;> simp [stateProductInfoFuel] at hInfo
          | _ => simp [stateProductInfoFuel] at hInfo
      | choice left right =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih left state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ index =>
                  cases index with
                  | zero =>
                      obtain ⟨hLeft, hRight⟩ :=
                        ih right state interface componentLeft componentRight q1 q2
                          (by
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [stateProductInfoFuel] using hInfo)
                      constructor <;> omega
                  | succ index => simp [stateProductInfoFuel] at hInfo
          | _ => simp [stateProductInfoFuel] at hInfo
      | fairChoice bid left right =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih left state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ index =>
                  cases index with
                  | zero =>
                      obtain ⟨hLeft, hRight⟩ :=
                        ih right state interface componentLeft componentRight q1 q2
                          (by
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [stateProductInfoFuel] using hInfo)
                      constructor <;> omega
                  | succ index => simp [stateProductInfoFuel] at hInfo
          | _ => simp [stateProductInfoFuel] at hInfo
      | seq left right =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih left state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ index =>
                  cases index with
                  | zero =>
                      obtain ⟨hLeft, hRight⟩ :=
                        ih right state interface componentLeft componentRight q1 q2
                          (by
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [stateProductInfoFuel] using hInfo)
                      constructor <;> omega
                  | succ index => simp [stateProductInfoFuel] at hInfo
          | _ => simp [stateProductInfoFuel] at hInfo
      | par left right productInterface =>
          cases state with
          | pair leftState rightState =>
              simp only [stateProductInfoFuel, Option.some.injEq,
                Prod.mk.injEq] at hInfo
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hInfo
              simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
              constructor <;> omega
          | _ => simp [stateProductInfoFuel] at hInfo
      | xoffer elseType branches =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih elseType state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ i =>
                  simp only [stateProductInfoFuel] at hInfo
                  cases hBranch : branches[i]? with
                  | none => simp [hBranch] at hInfo
                  | some branch =>
                      rcases branch with ⟨action, branchType⟩
                      obtain ⟨hLeft, hRight⟩ :=
                        ih branchType state interface componentLeft componentRight q1 q2
                          (by
                            have hMem : (action, branchType) ∈ branches :=
                              List.mem_iff_getElem?.mpr ⟨i, hBranch⟩
                            have hBranchFuel :=
                              typeCompilationFuel_le_typeBranchCompilationFuel branches
                                (action, branchType) hMem
                            have hBranchFuel' :
                                typeCompilationFuel branchType ≤
                                  typeBranchCompilationFuel branches := by
                              simpa using hBranchFuel
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [hBranch] using hInfo)
                      constructor <;> omega
          | _ => simp [stateProductInfoFuel] at hInfo
      | offer elseType branches =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih elseType state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ i =>
                  simp only [stateProductInfoFuel] at hInfo
                  cases hSelected : branches[i]? with
                  | none => simp [hSelected] at hInfo
                  | some selected =>
                      obtain ⟨hLeft, hRight⟩ :=
                        ih (parallelTypeBranchesSelecting selected branches) state
                          interface componentLeft componentRight q1 q2
                          (by
                            unfold TypeCompilationFuelSufficient
                            rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [hSelected] using hInfo)
                      constructor <;> omega
          | _ => simp [stateProductInfoFuel] at hInfo

private theorem computeFutureOfFuel_succ_stable :
    ∀ fuel signature processType state,
      TypeCompilationFuelSufficient processType fuel →
      computeFutureOfFuel signature (fuel + 1) processType state =
        computeFutureOfFuel signature fuel processType state := by
  intro fuel
  induction fuel with
  | zero =>
      intro signature processType state hFuel
      have hPositive := typeCompilationFuel_positive processType
      simp [TypeCompilationFuelSufficient] at hFuel
      omega
  | succ fuel ih =>
      intro signature processType state hFuel
      conv_lhs => rw [computeFutureOfFuel]
      conv_rhs => rw [computeFutureOfFuel]
      apply Finset.biUnion_congr rfl
      intro visited _hVisited
      cases hInfo : stateProductInfo processType visited with
      | none => simp
      | some info =>
          rcases info with ⟨interface, left, right, q1, q2⟩
          have hInfoFuel :
              stateProductInfoFuel (typeCompilationFuel processType)
                  processType visited = some (interface, left, right, q1, q2) := by
            simpa [stateProductInfo] using hInfo
          obtain ⟨hLeftLt, hRightLt⟩ :=
            stateProductInfoFuel_component_fuel_lt
              (typeCompilationFuel processType) processType visited interface
              left right q1 q2 (typeCompilationFuel_sufficient processType)
              hInfoFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient] at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient] at hFuel ⊢
            omega
          simp only
          rw [ih signature left q1 hLeftFuel, ih signature right q2 hRightFuel]

private theorem computeFutureOfFuel_add_stable
    (signature : TypeAlphabet) (processType : PactType)
    (state : TypeAutomatonState) (fuel extra : Nat)
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    computeFutureOfFuel signature (fuel + extra) processType state =
      computeFutureOfFuel signature fuel processType state := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        computeFutureOfFuel_succ_stable (fuel + extra) signature processType state
          (by
            simp [TypeCompilationFuelSufficient] at hFuel ⊢
            omega),
        ih]

/-- States that `computeFutureOfFuel` stabilizes once its fuel is sufficient, mirroring `compileTypeFuel_eq_of_sufficient`. -/
theorem computeFutureOfFuel_eq_of_sufficient
    (signature : TypeAlphabet) (processType : PactType) (state : TypeAutomatonState)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    computeFutureOfFuel signature leftFuel processType state =
      computeFutureOfFuel signature rightFuel processType state := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (computeFutureOfFuel_add_stable signature processType state leftFuel
      extra hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact computeFutureOfFuel_add_stable signature processType state rightFuel
      extra hRight

/-- Proves a `.child 0`-tagged state's future menu, in a compiled binary choice, agrees with the left child's own. -/
theorem computeFutureOf_binaryChoice_left
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel left)
      left).states) :
    computeFutureOf signature whole (.child 0 state) =
      computeFutureOf signature left state := by
  sorry

/-- Proves a `.child 1`-tagged state's future menu, in a compiled binary choice, agrees with the right child's own. -/
theorem computeFutureOf_binaryChoice_right
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel right + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel right)
      right).states) :
    computeFutureOf signature whole (.child 1 state) =
      computeFutureOf signature right state := by
  sorry

/-- Proves a `.child 0`-tagged state's future menu, in a compiled exclusive offer, agrees with the else child's own. -/
theorem computeFutureOf_exclusiveOffer_else
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildExclusiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2)))
    (hFuel : typeCompilationFuel elseType + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel elseType)
      elseType).states) :
    computeFutureOf signature whole (.child 0 state) =
      computeFutureOf signature elseType state := by
  sorry

/-- Proves a `.child (i+1)`-tagged state's future menu, in a compiled exclusive offer, agrees with branch `i`'s own. -/
theorem computeFutureOf_exclusiveOffer_branch
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildExclusiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2)))
    (i : Nat) (action : BareMessage) (branchType : PactType)
    (hBranch : branches[i]? = some (action, branchType))
    (hFuel : typeCompilationFuel branchType + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel branchType)
      branchType).states) :
    computeFutureOf signature whole (.child (i + 1) state) =
      computeFutureOf signature branchType state := by
  sorry


end

end Pact
