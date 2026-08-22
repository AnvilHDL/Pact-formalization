import Anvilpp.ProofHelpers.Regularity

namespace Pact

noncomputable section

open Classical

def TypeNonClockStep (source target : PactType) : Prop :=
  ∃ env label, TypeTransition env source label target ∧ ¬ label.isTock

/-- Zero or more non-clock semantic type steps. -/
def TypeSameCycleReaches (source target : PactType) : Prop :=
  Relation.ReflTransGen TypeNonClockStep source target

/-- A non-clock public automaton edge. -/
def AutomatonNonClockStep (automaton : TypeAutomaton)
    (source target : TypeAutomatonState) : Prop :=
  ∃ env label offers,
    automaton.HasEdge source env label offers target ∧ ¬ label.isTock

/-- A state reaches an accepting state without crossing a clock edge. -/
def AutomatonSameCycleReachesAccepting
    (automaton : TypeAutomaton) (state : TypeAutomatonState) : Prop :=
  ∃ finalState,
    Relation.ReflTransGen (AutomatonNonClockStep automaton) state finalState ∧
    finalState ∈ automaton.accepting

def ofStage (signature : TypeAlphabet) :
    Nat → PactType → TypeAutomatonState → Finset BareMessage
  | 0, _, _ => ∅
  | n + 1, processType, state =>
      (((compileTypeFuel signature (typeCompilationFuel processType)
          processType).edges.filter
          (fun edge => edge.source = state ∧ ¬ edge.label.semantic.isTock))).biUnion
        (fun edge => edge.current ∪ ofStage signature n processType edge.target) ∪
      (match stateProductInfo processType state with
        | some (interface, left, right, q1, q2) =>
            hideTypeOffers interface
              (ofStage signature n left q1 ∪ ofStage signature n right q2)
        | none => ∅)

lemma helper_h12_compiled_state_shape
    (signature : TypeAlphabet) {processType residual : PactType}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual (compileType signature processType).initial) :
    (compileType signature processType).initial ∈
      (compileType signature processType).states :=
  compileType_initial_mem signature processType

/-- Helper Lemma H15: future offers agree. -/
lemma helper_h15_future_offers_agree
    (signature : TypeAlphabet) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual state) :
    computeFutureOf signature processType state = typeFutureOffers residual := by
  sorry -- TODO(section7): prove by the constructor future-correctness bundle.

/-- Every local environment a signature generates is well-formed. -/
theorem H13_localEnvironment_wellFormed
    (signature : TypeAlphabet) {environment : TypeEnvironment}
    (hEnvironment : environment ∈ signature.localEnvironments) :
    environment.WellFormed := by
  simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image] at hEnvironment
  rcases hEnvironment with rfl | ⟨immediate, _hImmediate, future, hFuture, rfl⟩
  · simp [TypeEnvironment.WellFormed, TypeEnvironment.tock]
  · constructor
    · simp
    · intro _hClock
      change immediate ∩ future = ∅
      rw [← Finset.disjoint_iff_inter_eq_empty]
      apply Finset.disjoint_left.mpr
      intro action hImmediate hFutureMember
      have hAvailable := hFuture hFutureMember
      simp only [Finset.mem_sdiff] at hAvailable
      exact hAvailable.2 hImmediate

/-- Helper Lemma H12, binary choice/offer-root case, shared by `.choice` and
`.fairChoice`. -/
theorem helper_h12_binaryChoice_shape
    (signature : TypeAlphabet) (whole left right : PactType)
    (hUnfold :
      buildRelationSetCoreFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1) whole =
        insert (whole, TypeAutomatonState.root)
          ((buildRelationSetCoreFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left).image
              (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
            (buildRelationSetCoreFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right).image
              (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))))
    (hFuelEq : typeCompilationFuel whole =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet whole (compileType signature whole))
        residual state) :
    (residual = whole ∧ state = TypeAutomatonState.root) ∨
    (∃ q1, state = .child 0 q1 ∧
      relationMembership (buildRelationSet left (compileType signature left)) residual q1) ∨
    (∃ q2, state = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType signature right)) residual q2) := by
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature (typeCompilationFuel whole) whole := hRelated
  rw [hFuelEq, hUnfold] at hMem
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hR, hS⟩ | ⟨entry, hEntry, hR, hS⟩ | ⟨entry, hEntry, hR, hS⟩
  · exact Or.inl ⟨hR, hS⟩
  · refine Or.inr (Or.inl ⟨entry.2, hS.symm, ?_⟩)
    show (residual, entry.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel left) left
    rw [← buildRelationSetCoreFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl, ← hR]
    exact hEntry
  · refine Or.inr (Or.inr ⟨entry.2, hS.symm, ?_⟩)
    show (residual, entry.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel right) right
    rw [← buildRelationSetCoreFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl, ← hR]
    exact hEntry

theorem compileType_var_no_edge
    (signature : TypeAlphabet) (name : String)
    (source : TypeAutomatonState) (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    ¬ (compileType signature (.var name)).HasEdge source env label offers target := by
  intro hEdge
  have hSymbol := NewCorrespondence.compileType_hasEdge_symbol_mem signature (.var name) hEdge
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.var name) source target env label
      offers hSymbol).mp hEdge
  obtain ⟨pendingEdge, hMem, -, -, hLabel, -, -, -⟩ := hResolved
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image] at hMem
  obtain ⟨environment, -, hEq⟩ := hMem
  rw [← hEq] at hLabel
  simp at hLabel

theorem compileType_var_edges_empty
    (signature : TypeAlphabet) (name : String) :
    (compileType signature (.var name)).edges = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro edge hEdge
  exact compileType_var_no_edge signature name edge.source edge.symbol.environment
    edge.symbol.label edge.symbol.offers edge.target hEdge

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
      | skip => rfl
      | message _ _ => rfl
      | tock => rfl
      | progress _ => rfl
      | var _ => rfl
      | choice left right =>
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
      | fairChoice bid left right =>
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
      | seq left right =>
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
      | par left right interface =>
          cases state with
          | pair q1 q2 => rfl
          | _ => rfl
      | recur name body =>
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
      | xoffer elseType branches =>
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
      | offer elseType branches =>
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
                          typeCompilationFuel (parallelTypeBranchesSelecting selected branches) ≤
                            fuel := by
                        rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                        simp [typeCompilationFuel] at hFuel; omega
                      exact ih (parallelTypeBranchesSelecting selected branches) q hFuel'
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

theorem stateProductInfoFuel_eq_of_sufficient'
    (processType : PactType) (state : TypeAutomatonState)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    stateProductInfoFuel leftFuel processType state =
      stateProductInfoFuel rightFuel processType state := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (stateProductInfoFuel_add_stable processType state leftFuel extra hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact stateProductInfoFuel_add_stable processType state rightFuel extra hRight

/-- Tag-transparency for `.choice`/`.fairChoice`: `ofStage` at a `.child 0`-tagged
state agrees with `ofStage` inside `left`'s own automaton, at every stage. -/
theorem ofStage_binaryChoice_child0
    (signature : TypeAlphabet) (whole left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hEdgesEq : (compileTypeFuel signature (typeCompilationFuel whole) whole).edges =
      (buildChoiceAutomaton signature
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        selectionLeft selectionRight).edges)
    (hProductEq : ∀ q, stateProductInfo whole (TypeAutomatonState.child 0 q) =
      stateProductInfo left q) :
    ∀ m q, ofStage signature m whole (TypeAutomatonState.child 0 q) =
      ofStage signature m left q := by
  intro m
  induction m with
  | zero => intro q; rfl
  | succ m ih =>
      intro q
      simp only [ofStage]
      rw [hProductEq q, hEdgesEq]
      congr 1
      apply Finset.ext
      intro x
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨edge, ⟨hEdgeMem, hSource, hNotTock⟩, hx⟩
        obtain ⟨childEdge, hChildEdge, hChildSource, hEdgeEq⟩ :=
          (buildChoiceAutomaton_outgoing_left signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            selectionLeft selectionRight q edge).mp ⟨hEdgeMem, hSource⟩
        refine ⟨childEdge, ⟨hChildEdge, hChildSource, ?_⟩, ?_⟩
        · simpa [hEdgeEq, childPendingEdge] using hNotTock
        · rw [hEdgeEq] at hx
          simp only [childPendingEdge, childState] at hx
          rwa [ih childEdge.target] at hx
      · rintro ⟨childEdge, ⟨hChildMem, hChildSource, hNotTock⟩, hx⟩
        have hOut := (buildChoiceAutomaton_outgoing_left signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight q (childPendingEdge 0 childEdge)).mpr
          ⟨childEdge, hChildMem, hChildSource, rfl⟩
        refine ⟨childPendingEdge 0 childEdge, ⟨hOut.1, hOut.2, ?_⟩, ?_⟩
        · simpa [childPendingEdge] using hNotTock
        · simp only [childPendingEdge, childState]
          rwa [ih childEdge.target]

/-- Tag-transparency for `.choice`/`.fairChoice`, right side. -/
theorem ofStage_binaryChoice_child1
    (signature : TypeAlphabet) (whole left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hEdgesEq : (compileTypeFuel signature (typeCompilationFuel whole) whole).edges =
      (buildChoiceAutomaton signature
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        selectionLeft selectionRight).edges)
    (hProductEq : ∀ q, stateProductInfo whole (TypeAutomatonState.child 1 q) =
      stateProductInfo right q) :
    ∀ m q, ofStage signature m whole (TypeAutomatonState.child 1 q) =
      ofStage signature m right q := by
  intro m
  induction m with
  | zero => intro q; rfl
  | succ m ih =>
      intro q
      simp only [ofStage]
      rw [hProductEq q, hEdgesEq]
      congr 1
      apply Finset.ext
      intro x
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨edge, ⟨hEdgeMem, hSource, hNotTock⟩, hx⟩
        obtain ⟨childEdge, hChildEdge, hChildSource, hEdgeEq⟩ :=
          (buildChoiceAutomaton_outgoing_right signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            selectionLeft selectionRight q edge).mp ⟨hEdgeMem, hSource⟩
        refine ⟨childEdge, ⟨hChildEdge, hChildSource, ?_⟩, ?_⟩
        · simpa [hEdgeEq, childPendingEdge] using hNotTock
        · rw [hEdgeEq] at hx
          simp only [childPendingEdge, childState] at hx
          rwa [ih childEdge.target] at hx
      · rintro ⟨childEdge, ⟨hChildMem, hChildSource, hNotTock⟩, hx⟩
        have hOut := (buildChoiceAutomaton_outgoing_right signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight q (childPendingEdge 1 childEdge)).mpr
          ⟨childEdge, hChildMem, hChildSource, rfl⟩
        refine ⟨childPendingEdge 1 childEdge, ⟨hOut.1, hOut.2, ?_⟩, ?_⟩
        · simpa [childPendingEdge] using hNotTock
        · simp only [childPendingEdge, childState]
          rwa [ih childEdge.target]

theorem ofStage_futOffStage_agree (signature : TypeAlphabet) (processType : PactType) :
    ∀ n, ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet processType (compileType signature processType))
        residual state →
      ofStage signature n processType state = typeFutureOffersFuel n residual := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ k ih =>
    intro n
    induction n with
    | zero => intro residual state _; rfl
    | succ n innerIH =>
      intro residual state hRelated
      cases processType with
      | skip =>
          obtain ⟨hR, hS⟩ := NewCorrespondence.relationMembership_skip_cases signature hRelated
          subst hR; subst hS
          have hSelf : ofStage signature n .skip .root = ∅ := by
            have hIH := innerIH (buildRelationSet_initial .skip (compileType signature .skip))
            have hInit : (compileType signature .skip).initial = TypeAutomatonState.root := by
              simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
            rw [hInit] at hIH
            rw [hIH]
            cases n <;> rfl
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
            stateProductInfo, typeCompilationFuel, stateProductInfoFuel] at hx
          rcases hx with ⟨edge, ⟨hEdge, _⟩, hx⟩ | hx
          · simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_image, Finset.mem_filter] at hEdge
            obtain ⟨env, -, hEq⟩ := hEdge
            rw [← hEq] at hx
            simp only [hSelf] at hx
            simp at hx
          · simp at hx
      | var name =>
          unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
          simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_singleton,
            Prod.mk.injEq] at hRelated
          obtain ⟨hR, hS⟩ := hRelated
          subst hR; subst hS
          have hFinalEmpty : ofStage signature n (.var name) TypeAutomatonState.final = ∅ := by
            cases n with
            | zero => rfl
            | succ n =>
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro y hy
                simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                  stateProductInfo, typeCompilationFuel, stateProductInfoFuel] at hy
                rcases hy with ⟨edge, ⟨hEdge, hSource⟩, -⟩ | hy
                · simp only [compileTypeFuel, finishAutomatonFragment,
                    Finset.mem_image] at hEdge
                  obtain ⟨env, -, hEq⟩ := hEdge
                  rw [← hEq] at hSource
                  simp at hSource
                · simp at hy
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
            stateProductInfo, typeCompilationFuel, stateProductInfoFuel] at hx
          rcases hx with ⟨edge, ⟨hEdge, -⟩, hx⟩ | hx
          · simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_image] at hEdge
            obtain ⟨env, -, hEq⟩ := hEdge
            rw [← hEq] at hx
            simp only [hFinalEmpty] at hx
            simp at hx
          · simp at hx
      | message msg dir =>
          have hEdgeCases : ∀ edge ∈ (compileTypeFuel signature
              (typeCompilationFuel (.message msg dir)) (.message msg dir)).edges,
              (edge.source = TypeAutomatonState.root ∧ edge.current = {(msg, dir)} ∧
                edge.target = TypeAutomatonState.final) ∨
              (edge.source = TypeAutomatonState.root ∧ edge.current = {(msg, dir)} ∧
                edge.target = TypeAutomatonState.root) ∨
              (edge.source = TypeAutomatonState.final ∧ edge.current = ∅ ∧
                edge.target = TypeAutomatonState.final) := by
            intro edge hEdge
            simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
            rcases hEdge with (⟨env, -, hEq⟩ | ⟨env, -, hEq⟩) | ⟨env, -, hEq⟩
            · exact Or.inl (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩)
            · exact Or.inr (Or.inl (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩))
            · exact Or.inr (Or.inr (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩))
          have hFinalSelf : ofStage signature n (.message msg dir) TypeAutomatonState.final = ∅ := by
            have hFinalRelated :
                relationMembership
                  (buildRelationSet (.message msg dir) (compileType signature (.message msg dir)))
                  .skip TypeAutomatonState.final := by
              show (PactType.skip, TypeAutomatonState.final) ∈
                buildRelationSetCoreFuel signature (typeCompilationFuel (.message msg dir))
                  (.message msg dir)
              simp [typeCompilationFuel, buildRelationSetCoreFuel]
            have hIH := innerIH hFinalRelated
            rw [hIH]; cases n <;> rfl
          have hRootSelf : ofStage signature n (.message msg dir) TypeAutomatonState.root =
              typeFutureOffersFuel n (.message msg dir) := by
            have hIH := innerIH (buildRelationSet_initial (.message msg dir)
              (compileType signature (.message msg dir)))
            have hInit : (compileType signature (.message msg dir)).initial =
                TypeAutomatonState.root := by
              simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
            rwa [hInit] at hIH
          have hNoProduct : ∀ q, stateProductInfo (.message msg dir) q = none := by
            intro q
            simp [stateProductInfo, typeCompilationFuel, stateProductInfoFuel]
          have hEmptyLocal : TypeEnvironment.empty ∈ signature.localEnvironments := by
            simp only [TypeAlphabet.localEnvironments, Finset.mem_union, Finset.mem_biUnion,
              Finset.mem_powerset, Finset.mem_image]
            exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
          have hWitness : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
              (AutomatonConstructionLabel.visible TypeLabel.silent) {(msg, dir)}
              (FutureSpec.explicit ∅) TypeAutomatonState.root ∈
              (compileTypeFuel signature (typeCompilationFuel (.message msg dir))
                (.message msg dir)).edges := by
            simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter]
            refine Or.inl (Or.inr ⟨TypeEnvironment.empty, ⟨hEmptyLocal, rfl, ?_⟩, rfl⟩)
            simp [TypeEnvironment.hasNeed, TypeEnvironment.empty]
          obtain ⟨hR, hS⟩ | ⟨hR, hS⟩ :=
            NewCorrespondence.relationMembership_message_cases signature msg dir hRelated
          · subst hR; subst hS
            apply Finset.ext
            intro x
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false, typeFutureOffersFuel,
              Finset.mem_singleton]
            constructor
            · rintro ⟨edge, hEdge, hx⟩
              rcases hEdgeCases edge hEdge.1 with ⟨-, hCurrent, hTarget⟩ | ⟨-, hCurrent, hTarget⟩ |
                  ⟨hSource, -, -⟩
              · rw [hCurrent, hTarget, hFinalSelf] at hx
                rcases hx with hx | hx
                · exact Finset.mem_singleton.mp hx
                · simp at hx
              · rw [hCurrent, hTarget, hRootSelf] at hx
                rcases hx with hx | hx
                · exact Finset.mem_singleton.mp hx
                · cases n with
                  | zero => exact absurd hx (Finset.notMem_empty _)
                  | succ n => simpa [typeFutureOffersFuel] using hx
              · exact absurd hEdge.2 (by rw [hSource]; simp)
            · intro hx
              subst hx
              exact ⟨_, ⟨hWitness, by
                simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.silent]⟩,
                Or.inl (Finset.mem_singleton_self _)⟩
          · subst hR; subst hS
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨hSource, -, -⟩ | ⟨hSource, -, -⟩ |
                ⟨-, hCurrent, hTarget⟩
            · exact absurd hEdge.2 (by rw [hSource]; simp)
            · exact absurd hEdge.2 (by rw [hSource]; simp)
            · rw [hCurrent, hTarget, hFinalSelf] at hx
              simpa using hx
      | tock =>
          have hEdgeCases : ∀ edge ∈ (compileTypeFuel signature
              (typeCompilationFuel .tock) .tock).edges,
              (edge.source = TypeAutomatonState.root ∧ edge.current = ∅ ∧
                (edge.target = TypeAutomatonState.final ∨
                  edge.target = TypeAutomatonState.root)) ∨
              (edge.source = TypeAutomatonState.final ∧ edge.current = ∅ ∧
                edge.target = TypeAutomatonState.final) := by
            intro edge hEdge
            simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image] at hEdge
            rcases hEdge with ⟨env, -, hEq⟩ | ⟨env, -, hEq⟩
            · split at hEq <;> exact Or.inl (by rw [← hEq]; simp)
            · exact Or.inr (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩)
          have hNoProduct : ∀ q, stateProductInfo .tock q = none := by
            intro q; simp [stateProductInfo, typeCompilationFuel, stateProductInfoFuel]
          have hFinalSelf : ofStage signature n .tock TypeAutomatonState.final = ∅ := by
            have hFinalRelated :
                relationMembership (buildRelationSet .tock (compileType signature .tock))
                  .skip TypeAutomatonState.final := by
              show (PactType.skip, TypeAutomatonState.final) ∈
                buildRelationSetCoreFuel signature (typeCompilationFuel .tock) .tock
              simp [typeCompilationFuel, buildRelationSetCoreFuel]
            have hIH := innerIH hFinalRelated
            rw [hIH]; cases n <;> rfl
          have hRootSelf : ofStage signature n .tock TypeAutomatonState.root = ∅ := by
            have hIH := innerIH (buildRelationSet_initial .tock (compileType signature .tock))
            have hInit : (compileType signature .tock).initial = TypeAutomatonState.root := by
              simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
            rw [hInit] at hIH
            rw [hIH]; cases n <;> rfl
          obtain ⟨hR, hS⟩ | ⟨hR, hS⟩ :=
            NewCorrespondence.relationMembership_tock_cases signature hRelated
          · subst hR; subst hS
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨-, hCurrent, hTarget⟩ | ⟨hSource, -, -⟩
            · rw [hCurrent] at hx
              rcases hTarget with hTarget | hTarget
              · rw [hTarget, hFinalSelf] at hx; simpa using hx
              · rw [hTarget, hRootSelf] at hx; simpa using hx
            · exact absurd hEdge.2 (by rw [hSource]; simp)
          · subst hR; subst hS
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨hSource, -, -⟩ | ⟨-, hCurrent, hTarget⟩
            · exact absurd hEdge.2 (by rw [hSource]; simp)
            · rw [hCurrent, hTarget, hFinalSelf] at hx
              simpa using hx
      | progress pid =>
          have hEdgeCases : ∀ edge ∈ (compileTypeFuel signature
              (typeCompilationFuel (.progress pid)) (.progress pid)).edges,
              (edge.source = TypeAutomatonState.root ∧ edge.current = ∅ ∧
                edge.target = TypeAutomatonState.final) ∨
              (edge.source = TypeAutomatonState.final ∧ edge.current = ∅ ∧
                edge.target = TypeAutomatonState.final) := by
            intro edge hEdge
            simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
            rcases hEdge with ⟨env, -, hEq⟩ | ⟨env, -, hEq⟩
            · exact Or.inl (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩)
            · exact Or.inr (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩)
          have hNoProduct : ∀ q, stateProductInfo (.progress pid) q = none := by
            intro q; simp [stateProductInfo, typeCompilationFuel, stateProductInfoFuel]
          have hFinalSelf : ofStage signature n (.progress pid) TypeAutomatonState.final = ∅ := by
            have hFinalRelated :
                relationMembership
                  (buildRelationSet (.progress pid) (compileType signature (.progress pid)))
                  .skip TypeAutomatonState.final := by
              show (PactType.skip, TypeAutomatonState.final) ∈
                buildRelationSetCoreFuel signature (typeCompilationFuel (.progress pid))
                  (.progress pid)
              simp [typeCompilationFuel, buildRelationSetCoreFuel]
            have hIH := innerIH hFinalRelated
            rw [hIH]; cases n <;> rfl
          obtain ⟨hR, hS⟩ | ⟨hR, hS⟩ :=
            NewCorrespondence.relationMembership_progress_cases signature pid hRelated
          · subst hR; subst hS
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨-, hCurrent, hTarget⟩ | ⟨hSource, -, -⟩
            · rw [hCurrent, hTarget, hFinalSelf] at hx; simpa using hx
            · exact absurd hEdge.2 (by rw [hSource]; simp)
          · subst hR; subst hS
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨hSource, -, -⟩ | ⟨-, hCurrent, hTarget⟩
            · exact absurd hEdge.2 (by rw [hSource]; simp)
            · rw [hCurrent, hTarget, hFinalSelf] at hx; simpa using hx
      | choice left right =>
          have hLeftSize : sizeOf left < k := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < k := by rw [← hSize]; simp_wf; omega
          have hFuelEq : typeCompilationFuel (.choice left right) =
              max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
            simp only [typeCompilationFuel]; omega
          have hWhole :
              compileTypeFuel signature (typeCompilationFuel (.choice left right))
                (.choice left right) =
                buildChoiceAutomaton signature
                  (compileTypeFuel signature (typeCompilationFuel left) left)
                  (compileTypeFuel signature (typeCompilationFuel right) right)
                  TypeLabel.silent TypeLabel.silent := by
            rw [hFuelEq]
            show buildChoiceAutomaton signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
                TypeLabel.silent TypeLabel.silent =
              buildChoiceAutomaton signature (compileTypeFuel signature
                (typeCompilationFuel left) left) (compileTypeFuel signature
                (typeCompilationFuel right) right) TypeLabel.silent TypeLabel.silent
            rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
              compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
          have hProductEq0 : ∀ q, stateProductInfo (.choice left right)
              (TypeAutomatonState.child 0 q) = stateProductInfo left q := by
            intro q
            show stateProductInfoFuel (typeCompilationFuel (.choice left right))
              (.choice left right) (.child 0 q) =
              stateProductInfoFuel (typeCompilationFuel left) left q
            rw [hFuelEq]
            exact stateProductInfoFuel_eq_of_sufficient' left q (le_max_left _ _) le_rfl
          have hProductEq1 : ∀ q, stateProductInfo (.choice left right)
              (TypeAutomatonState.child 1 q) = stateProductInfo right q := by
            intro q
            show stateProductInfoFuel (typeCompilationFuel (.choice left right))
              (.choice left right) (.child 1 q) =
              stateProductInfoFuel (typeCompilationFuel right) right q
            rw [hFuelEq]
            exact stateProductInfoFuel_eq_of_sufficient' right q (le_max_right _ _) le_rfl
          have hTag0 := ofStage_binaryChoice_child0 signature (.choice left right) left right
            TypeLabel.silent TypeLabel.silent (by rw [hWhole]) hProductEq0
          have hTag1 := ofStage_binaryChoice_child1 signature (.choice left right) left right
            TypeLabel.silent TypeLabel.silent (by rw [hWhole]) hProductEq1
          have hShape := helper_h12_binaryChoice_shape signature (.choice left right) left right
            rfl hFuelEq hRelated
          rcases hShape with ⟨hResidualEq, hStateEq⟩ |
            ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
          · subst hResidualEq; subst hStateEq
            have hEmptyLocal : TypeEnvironment.empty ∈ signature.localEnvironments := by
              simp only [TypeAlphabet.localEnvironments, Finset.mem_union, Finset.mem_biUnion,
                Finset.mem_powerset, Finset.mem_image]
              exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
            have hNoProductRoot : stateProductInfo (.choice left right)
                TypeAutomatonState.root = none := by
              show stateProductInfoFuel (typeCompilationFuel (.choice left right))
                (.choice left right) TypeAutomatonState.root = none
              rw [hFuelEq]; rfl
            have hWitness0 : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
                (AutomatonConstructionLabel.visible TypeLabel.silent) ∅
                (FutureSpec.at (TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∅)
                (TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∈
                (compileTypeFuel signature (typeCompilationFuel (.choice left right))
                  (.choice left right)).edges := by
              rw [hWhole]
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childState,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨TypeEnvironment.empty, hEmptyLocal, Or.inl rfl⟩
            have hWitness1 : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
                (AutomatonConstructionLabel.visible TypeLabel.silent) ∅
                (FutureSpec.at (TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) ∅)
                (TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) ∈
                (compileTypeFuel signature (typeCompilationFuel (.choice left right))
                  (.choice left right)).edges := by
              rw [hWhole]
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childState,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨TypeEnvironment.empty, hEmptyLocal, Or.inr rfl⟩
            have hEdgeSourceCases : ∀ edge ∈ (compileTypeFuel signature
                (typeCompilationFuel (.choice left right)) (.choice left right)).edges,
                edge.source = TypeAutomatonState.root →
                (edge.current = ∅ ∧ edge.target = TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∨
                (edge.current = ∅ ∧ edge.target = TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) := by
              intro edge hEdge hSource
              rw [hWhole] at hEdge
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
                childState, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
                Finset.mem_insert, Finset.mem_singleton] at hEdge
              rcases hEdge with (⟨childEdge, -, hEq⟩ | ⟨childEdge, -, hEq⟩) |
                ⟨environment, -, hEq | hEq⟩
              · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
              · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
              · left; rw [hEq]; exact ⟨rfl, rfl⟩
              · right; rw [hEq]; exact ⟨rfl, rfl⟩
            apply Finset.ext
            intro x
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProductRoot, Finset.notMem_empty, or_false]
            constructor
            · rintro ⟨edge, ⟨hEdgeMem, hEdgeSource, -⟩, hx⟩
              rcases hEdgeSourceCases edge hEdgeMem hEdgeSource with
                ⟨hCurrent, hTarget⟩ | ⟨hCurrent, hTarget⟩
              · simp only [hCurrent, hTarget, Finset.notMem_empty, false_or] at hx
                rw [hTag0 n
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial] at hx
                have hLeftInitRelated := buildRelationSet_initial left (compileType signature left)
                simp only [compileType] at hLeftInitRelated
                rw [ih (sizeOf left) hLeftSize left rfl n hLeftInitRelated] at hx
                simp only [typeFutureOffersFuel, Finset.mem_union]
                exact Or.inl hx
              · simp only [hCurrent, hTarget, Finset.notMem_empty, false_or] at hx
                rw [hTag1 n
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial] at hx
                have hRightInitRelated := buildRelationSet_initial right
                  (compileType signature right)
                simp only [compileType] at hRightInitRelated
                rw [ih (sizeOf right) hRightSize right rfl n hRightInitRelated] at hx
                simp only [typeFutureOffersFuel, Finset.mem_union]
                exact Or.inr hx
            · intro hx
              simp only [typeFutureOffersFuel, Finset.mem_union] at hx
              rcases hx with hx | hx
              · refine ⟨_, ⟨hWitness0, rfl, ?_⟩, ?_⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.silent]
                · right
                  rw [hTag0 n
                    (compileTypeFuel signature (typeCompilationFuel left) left).initial]
                  have hLeftInitRelated := buildRelationSet_initial left
                    (compileType signature left)
                  simp only [compileType] at hLeftInitRelated
                  rwa [ih (sizeOf left) hLeftSize left rfl n hLeftInitRelated]
              · refine ⟨_, ⟨hWitness1, rfl, ?_⟩, ?_⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.silent]
                · right
                  rw [hTag1 n
                    (compileTypeFuel signature (typeCompilationFuel right) right).initial]
                  have hRightInitRelated := buildRelationSet_initial right
                    (compileType signature right)
                  simp only [compileType] at hRightInitRelated
                  rwa [ih (sizeOf right) hRightSize right rfl n hRightInitRelated]
          · subst hStateEq
            rw [hTag0 (n + 1) q]
            exact ih (sizeOf left) hLeftSize left rfl (n + 1) hLeftRelated
          · subst hStateEq
            rw [hTag1 (n + 1) q]
            exact ih (sizeOf right) hRightSize right rfl (n + 1) hRightRelated
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < k := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < k := by rw [← hSize]; simp_wf; omega
          have hFuelEq : typeCompilationFuel (.fairChoice bid left right) =
              max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
            simp only [typeCompilationFuel]; omega
          have hWhole :
              compileTypeFuel signature (typeCompilationFuel (.fairChoice bid left right))
                (.fairChoice bid left right) =
                buildChoiceAutomaton signature
                  (compileTypeFuel signature (typeCompilationFuel left) left)
                  (compileTypeFuel signature (typeCompilationFuel right) right)
                  (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
            rw [hFuelEq]
            show buildChoiceAutomaton signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
              buildChoiceAutomaton signature (compileTypeFuel signature
                (typeCompilationFuel left) left) (compileTypeFuel signature
                (typeCompilationFuel right) right) (TypeLabel.fair bid true)
                (TypeLabel.fair bid false)
            rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
              compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
          have hProductEq0 : ∀ q, stateProductInfo (.fairChoice bid left right)
              (TypeAutomatonState.child 0 q) = stateProductInfo left q := by
            intro q
            show stateProductInfoFuel (typeCompilationFuel (.fairChoice bid left right))
              (.fairChoice bid left right) (.child 0 q) =
              stateProductInfoFuel (typeCompilationFuel left) left q
            rw [hFuelEq]
            exact stateProductInfoFuel_eq_of_sufficient' left q (le_max_left _ _) le_rfl
          have hProductEq1 : ∀ q, stateProductInfo (.fairChoice bid left right)
              (TypeAutomatonState.child 1 q) = stateProductInfo right q := by
            intro q
            show stateProductInfoFuel (typeCompilationFuel (.fairChoice bid left right))
              (.fairChoice bid left right) (.child 1 q) =
              stateProductInfoFuel (typeCompilationFuel right) right q
            rw [hFuelEq]
            exact stateProductInfoFuel_eq_of_sufficient' right q (le_max_right _ _) le_rfl
          have hTag0 := ofStage_binaryChoice_child0 signature (.fairChoice bid left right)
            left right (TypeLabel.fair bid true) (TypeLabel.fair bid false)
            (by rw [hWhole]) hProductEq0
          have hTag1 := ofStage_binaryChoice_child1 signature (.fairChoice bid left right)
            left right (TypeLabel.fair bid true) (TypeLabel.fair bid false)
            (by rw [hWhole]) hProductEq1
          have hShape := helper_h12_binaryChoice_shape signature (.fairChoice bid left right)
            left right rfl hFuelEq hRelated
          rcases hShape with ⟨hResidualEq, hStateEq⟩ |
            ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
          · subst hResidualEq; subst hStateEq
            have hEmptyLocal : TypeEnvironment.empty ∈ signature.localEnvironments := by
              simp only [TypeAlphabet.localEnvironments, Finset.mem_union, Finset.mem_biUnion,
                Finset.mem_powerset, Finset.mem_image]
              exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
            have hNoProductRoot : stateProductInfo (.fairChoice bid left right)
                TypeAutomatonState.root = none := by
              show stateProductInfoFuel (typeCompilationFuel (.fairChoice bid left right))
                (.fairChoice bid left right) TypeAutomatonState.root = none
              rw [hFuelEq]; rfl
            have hWitness0 : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
                (AutomatonConstructionLabel.visible (TypeLabel.fair bid true)) ∅
                (FutureSpec.at (TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∅)
                (TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∈
                (compileTypeFuel signature (typeCompilationFuel (.fairChoice bid left right))
                  (.fairChoice bid left right)).edges := by
              rw [hWhole]
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childState,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨TypeEnvironment.empty, hEmptyLocal, Or.inl rfl⟩
            have hWitness1 : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
                (AutomatonConstructionLabel.visible (TypeLabel.fair bid false)) ∅
                (FutureSpec.at (TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) ∅)
                (TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) ∈
                (compileTypeFuel signature (typeCompilationFuel (.fairChoice bid left right))
                  (.fairChoice bid left right)).edges := by
              rw [hWhole]
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childState,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨TypeEnvironment.empty, hEmptyLocal, Or.inr rfl⟩
            have hEdgeSourceCases : ∀ edge ∈ (compileTypeFuel signature
                (typeCompilationFuel (.fairChoice bid left right))
                (.fairChoice bid left right)).edges,
                edge.source = TypeAutomatonState.root →
                (edge.current = ∅ ∧ edge.target = TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∨
                (edge.current = ∅ ∧ edge.target = TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) := by
              intro edge hEdge hSource
              rw [hWhole] at hEdge
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
                childState, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
                Finset.mem_insert, Finset.mem_singleton] at hEdge
              rcases hEdge with (⟨childEdge, -, hEq⟩ | ⟨childEdge, -, hEq⟩) |
                ⟨environment, -, hEq | hEq⟩
              · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
              · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
              · left; rw [hEq]; exact ⟨rfl, rfl⟩
              · right; rw [hEq]; exact ⟨rfl, rfl⟩
            apply Finset.ext
            intro x
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProductRoot, Finset.notMem_empty, or_false]
            constructor
            · rintro ⟨edge, ⟨hEdgeMem, hEdgeSource, -⟩, hx⟩
              rcases hEdgeSourceCases edge hEdgeMem hEdgeSource with
                ⟨hCurrent, hTarget⟩ | ⟨hCurrent, hTarget⟩
              · simp only [hCurrent, hTarget, Finset.notMem_empty, false_or] at hx
                rw [hTag0 n
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial] at hx
                have hLeftInitRelated := buildRelationSet_initial left (compileType signature left)
                simp only [compileType] at hLeftInitRelated
                rw [ih (sizeOf left) hLeftSize left rfl n hLeftInitRelated] at hx
                simp only [typeFutureOffersFuel, Finset.mem_union]
                exact Or.inl hx
              · simp only [hCurrent, hTarget, Finset.notMem_empty, false_or] at hx
                rw [hTag1 n
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial] at hx
                have hRightInitRelated := buildRelationSet_initial right
                  (compileType signature right)
                simp only [compileType] at hRightInitRelated
                rw [ih (sizeOf right) hRightSize right rfl n hRightInitRelated] at hx
                simp only [typeFutureOffersFuel, Finset.mem_union]
                exact Or.inr hx
            · intro hx
              simp only [typeFutureOffersFuel, Finset.mem_union] at hx
              rcases hx with hx | hx
              · refine ⟨_, ⟨hWitness0, rfl, ?_⟩, ?_⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.fair]
                · right
                  rw [hTag0 n
                    (compileTypeFuel signature (typeCompilationFuel left) left).initial]
                  have hLeftInitRelated := buildRelationSet_initial left
                    (compileType signature left)
                  simp only [compileType] at hLeftInitRelated
                  rwa [ih (sizeOf left) hLeftSize left rfl n hLeftInitRelated]
              · refine ⟨_, ⟨hWitness1, rfl, ?_⟩, ?_⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.fair]
                · right
                  rw [hTag1 n
                    (compileTypeFuel signature (typeCompilationFuel right) right).initial]
                  have hRightInitRelated := buildRelationSet_initial right
                    (compileType signature right)
                  simp only [compileType] at hRightInitRelated
                  rwa [ih (sizeOf right) hRightSize right rfl n hRightInitRelated]
          · subst hStateEq
            rw [hTag0 (n + 1) q]
            exact ih (sizeOf left) hLeftSize left rfl (n + 1) hLeftRelated
          · subst hStateEq
            rw [hTag1 (n + 1) q]
            exact ih (sizeOf right) hRightSize right rfl (n + 1) hRightRelated
      | _ => sorry

/-- `ty.replaceVar var replacement = .skip ↔ ty = .skip`, given `replacement ≠ .skip`. -/
theorem replaceVar_eq_skip_iff (ty : PactType) (var : String) (replacement : PactType)
    (hReplacement : replacement ≠ .skip) :
    ty.replaceVar var replacement = .skip ↔ ty = .skip := by
  cases ty with
  | var other =>
      simp only [PactType.replaceVar]
      split
      · simp [hReplacement]
      · simp
  | skip => simp [PactType.replaceVar]
  | message _ _ => simp [PactType.replaceVar]
  | progress _ => simp [PactType.replaceVar]
  | tock => simp [PactType.replaceVar]
  | choice _ _ => simp [PactType.replaceVar]
  | seq _ _ => simp [PactType.replaceVar]
  | par _ _ _ => simp [PactType.replaceVar]
  | recur _ _ => simp only [PactType.replaceVar]; split <;> simp
  | fairChoice _ _ _ => simp [PactType.replaceVar]
  | xoffer _ _ => simp [PactType.replaceVar]
  | offer _ _ => simp [PactType.replaceVar]

/-- H13 for any `.par _ _ _` node, unconditionally. -/
theorem helper_h13_par_case
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.par left right interface)
        (compileType signature (.par left right interface))) residual state) :
    state ∈ (compileType signature (.par left right interface)).accepting ↔
      residual = .skip := by
  have hFuelEq : typeCompilationFuel (.par left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hAcceptEq : (compileType signature (.par left right interface)).accepting =
      {TypeAutomatonState.final} := by
    show (compileTypeFuel signature (typeCompilationFuel (.par left right interface))
      (.par left right interface)).accepting = _
    rw [hFuelEq]
    show (buildParallelAutomaton signature interface
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right)).accepting = _
    simp [buildParallelAutomaton, finishAutomatonFragment]
  rw [hAcceptEq]
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature (typeCompilationFuel (.par left right interface))
        (.par left right interface) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image,
    Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidualEq, hStateEq⟩ | ⟨entry, -, hR, hS⟩
  · subst hResidualEq; subst hStateEq; simp
  · subst hR; subst hS; simp

/-- H13 for any `.seq first second`, given H13 for `second` alone. -/
theorem helper_h13_seq_case
    (signature : TypeAlphabet) (first second : PactType)
    (hSecondH13 : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet second (compileType signature second)) residual
        state →
      (state ∈ (compileType signature second).accepting ↔ residual = .skip))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.seq first second) (compileType signature (.seq first second)))
      residual state) :
    state ∈ (compileType signature (.seq first second)).accepting ↔ residual = .skip := by
  have hFuelEq : typeCompilationFuel (.seq first second) =
      max (typeCompilationFuel first) (typeCompilationFuel second) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hAcceptEq : (compileType signature (.seq first second)).accepting =
      childAccepting 1 (compileTypeFuel signature (typeCompilationFuel second) second) := by
    show (compileTypeFuel signature (typeCompilationFuel (.seq first second))
      (.seq first second)).accepting = _
    rw [hFuelEq]
    show (buildSequenceAutomaton signature
      (compileTypeFuel signature
        (max (typeCompilationFuel first) (typeCompilationFuel second)) first)
      (compileTypeFuel signature
        (max (typeCompilationFuel first) (typeCompilationFuel second)) second)).accepting = _
    rw [compileTypeFuel_eq_of_sufficient signature second (le_max_right _ _) le_rfl]
    simp [buildSequenceAutomaton, finishAutomatonFragment]
  rw [hAcceptEq]
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature (typeCompilationFuel (.seq first second))
        (.seq first second) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image, Prod.mk.injEq]
    at hMem
  rcases hMem with ⟨entry, hEntry, hR, hS⟩ | ⟨entry, hEntry, hR, hS⟩
  · subst hR; subst hS
    simp only [childAccepting, Finset.mem_image, childState]
    constructor
    · rintro ⟨q', -, hEq⟩
      injection hEq with hIdx _
      omega
    · intro hSkip
      exact absurd hSkip (by simp)
  · subst hR; subst hS
    have hEntryRelated :
        relationMembership (buildRelationSet second (compileType signature second))
          entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel signature (typeCompilationFuel second) second
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature second
        (le_max_right _ _) le_rfl]
      exact hEntry
    have hIH := hSecondH13 hEntryRelated
    simp only [childAccepting, Finset.mem_image, childState]
    constructor
    · rintro ⟨q', hq', hEq⟩
      injection hEq with _ hEq'
      exact hIH.mp (hEq' ▸ hq')
    · intro hSkip
      exact ⟨entry.2, hIH.mpr hSkip, rfl⟩

/-- H13 for any `.xoffer elseType branches`, given H13 for `elseType` and for
every branch's continuation type. -/
theorem helper_h13_xoffer_case
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseH13 : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet elseType (compileType signature elseType)) residual
        state →
      (state ∈ (compileType signature elseType).accepting ↔ residual = .skip))
    (hBranchesH13 : ∀ branch ∈ branches, ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet branch.2 (compileType signature branch.2)) residual
        state →
      (state ∈ (compileType signature branch.2).accepting ↔ residual = .skip))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.xoffer elseType branches)
        (compileType signature (.xoffer elseType branches))) residual state) :
    state ∈ (compileType signature (.xoffer elseType branches)).accepting ↔
      residual = .skip := by
  have hFuelEq : typeCompilationFuel (.xoffer elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hAcceptEq : (compileType signature (.xoffer elseType branches)).accepting =
      childAccepting 0 (compileTypeFuel signature (typeCompilationFuel elseType) elseType) ∪
        indexedFragmentAccepting (branches.map fun branch =>
          (branch.1, compileTypeFuel signature (typeCompilationFuel branch.2) branch.2)) := by
    show (compileTypeFuel signature (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches)).accepting = _
    rw [hFuelEq]
    show (buildExclusiveOfferAutomaton signature branches
      (compileTypeFuel signature
        (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches)) elseType)
      (branches.map fun branch => (branch.1, compileTypeFuel signature
        (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches))
        branch.2))).accepting = _
    rw [compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl]
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment]
    congr 2
    apply List.map_congr_left
    intro branch hBranch
    congr 1
    exact compileTypeFuel_eq_of_sufficient signature branch.2
      (le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch)
        (le_max_right _ _)) le_rfl
  rw [hAcceptEq]
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature (typeCompilationFuel (.xoffer elseType branches))
        (.xoffer elseType branches) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    mem_foldl_union_iff, Finset.notMem_empty, false_or, Finset.mem_image,
    Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidualEq, hStateEq⟩ | ⟨a, ha, hR, hS⟩ |
    ⟨item, hItem, a, ha, hR, hS⟩
  · subst hResidualEq; subst hStateEq
    simp [childAccepting, childState, indexedFragmentAccepting, mem_foldl_union_iff]
  · subst hR; subst hS
    have hEntryRelated :
        relationMembership (buildRelationSet elseType (compileType signature elseType))
          a.1 a.2 := by
      show (a.1, a.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel elseType)
        elseType
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature elseType
        (le_max_left _ _) le_rfl]
      exact ha
    have hIH := hElseH13 hEntryRelated
    simp only [Finset.mem_union, childAccepting, Finset.mem_image, childState,
      indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
    constructor
    · rintro (⟨q', hq', hEq⟩ | ⟨item', hItem', q', -, hEq⟩)
      · injection hEq with _ hEq'
        exact hIH.mp (hEq' ▸ hq')
      · exact nomatch hEq
    · intro hSkip
      exact Or.inl ⟨a.2, hIH.mpr hSkip, rfl⟩
  · subst hR; subst hS
    have hMemBranches : item.1 ∈ branches := by
      have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
      exact List.mem_of_getElem? hGet
    have hItemFuel : typeCompilationFuel item.1.2 ≤
        max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) :=
      le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches item.1 hMemBranches)
        (le_max_right _ _)
    have hEntryRelated :
        relationMembership (buildRelationSet item.1.2 (compileType signature item.1.2))
          a.1 a.2 := by
      show (a.1, a.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel item.1.2)
        item.1.2
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature item.1.2 hItemFuel le_rfl]
      exact ha
    have hIH := hBranchesH13 item.1 hMemBranches hEntryRelated
    have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
    have hMapGet :
        (branches.map fun branch => (branch.1,
          compileTypeFuel signature (typeCompilationFuel branch.2) branch.2))[item.2]? =
          some (item.1.1, compileTypeFuel signature (typeCompilationFuel item.1.2) item.1.2) := by
      rw [List.getElem?_map, hGet]; rfl
    simp only [Finset.mem_union, childAccepting, Finset.mem_image, childState,
      indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
    constructor
    · rintro (⟨q1, hq1, hEq1⟩ | ⟨item', hItem', q2, hq2, hEq2⟩)
      · exact nomatch hEq1
      · injection hEq2 with hIdxEq hQEq
        have hItemEq : item'.1 =
            (item.1.1, compileTypeFuel signature (typeCompilationFuel item.1.2) item.1.2) := by
          have hGet' := List.mk_mem_zipIdx_iff_getElem?.mp hItem'
          have hIdxEq' : item'.2 = item.2 := by omega
          rw [hIdxEq'] at hGet'
          rw [hMapGet] at hGet'
          injection hGet' with hFst
          exact hFst.symm
        rw [hItemEq] at hq2
        exact hIH.mp (hQEq ▸ hq2)
    · intro hSkip
      refine Or.inr ⟨((item.1.1,
          compileTypeFuel signature (typeCompilationFuel item.1.2) item.1.2), item.2),
        List.mk_mem_zipIdx_iff_getElem?.mpr hMapGet, a.2, hIH.mpr hSkip, rfl⟩

/-- H13 for `parallelTypeBranchesSelecting selected branches`, given H13 for
every branch's own continuation type. -/
theorem helper_h13_parallelTypeBranchesSelecting
    (signature : TypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranchesH13 : ∀ branch ∈ branches, ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet branch.2 (compileType signature branch.2)) residual
        state →
      (state ∈ (compileType signature branch.2).accepting ↔ residual = .skip))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (parallelTypeBranchesSelecting selected branches)
        (compileType signature (parallelTypeBranchesSelecting selected branches)))
      residual state) :
    state ∈ (compileType signature (parallelTypeBranchesSelecting selected branches)).accepting ↔
      residual = .skip := by
  match branches with
  | [] =>
      simp only [parallelTypeBranchesSelecting] at hRelated ⊢
      obtain ⟨hR, hS⟩ := NewCorrespondence.relationMembership_skip_cases signature hRelated
      subst hR; subst hS
      simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  | [branch] =>
      simp only [parallelTypeBranchesSelecting] at hRelated ⊢
      by_cases hSel : branch = selected
      · rw [if_pos hSel] at hRelated ⊢
        simp only [selectedTypeBranch] at hRelated ⊢
        exact helper_h13_seq_case signature (.message branch.1.1 branch.1.2) branch.2
          (hBranchesH13 branch (by simp)) hRelated
      · rw [if_neg hSel] at hRelated ⊢
        simp only [singletonTypeXOffer] at hRelated ⊢
        exact helper_h13_xoffer_case signature .skip [branch]
          (fun hR => by
            obtain ⟨hR', hS'⟩ := NewCorrespondence.relationMembership_skip_cases signature hR
            subst hR'; subst hS'
            simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment])
          (by
            intro branch' hBranch' residual state hR
            have hEq : branch' = branch := by simpa using hBranch'
            rw [hEq] at hR ⊢
            exact hBranchesH13 branch (by simp) hR)
          hRelated
  | branch :: b2 :: rest =>
      simp only [parallelTypeBranchesSelecting] at hRelated ⊢
      by_cases hSel : branch = selected
      · rw [if_pos hSel] at hRelated ⊢
        exact helper_h13_par_case signature _ _ ∅ hRelated
      · rw [if_neg hSel] at hRelated ⊢
        exact helper_h13_par_case signature _ _ ∅ hRelated

/-- Helper Lemma H13: final states represent completion. -/
lemma helper_h13_final_states_represent_completion
    (signature : TypeAlphabet) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual state) :
    state ∈ (compileType signature processType).accepting ↔ residual = .skip := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType residual state with
  | _ n ih =>
    cases processType with
    | skip =>
        obtain ⟨hResidual, hState⟩ :=
          NewCorrespondence.relationMembership_skip_cases signature hRelated
        subst hResidual; subst hState
        simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | message msg dir =>
        rcases NewCorrespondence.relationMembership_message_cases signature msg dir hRelated with
          ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState <;>
          simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | tock =>
        rcases NewCorrespondence.relationMembership_tock_cases signature hRelated with
          ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState <;>
          simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | progress pid =>
        rcases NewCorrespondence.relationMembership_progress_cases signature pid hRelated with
          ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState <;>
          simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | var name =>
        unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
        simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_singleton,
          Prod.mk.injEq] at hRelated
        obtain ⟨hResidualEq, hStateEq⟩ := hRelated
        subst hResidualEq; subst hStateEq
        simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | choice left right =>
        have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
        have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
        have hFuelEq : typeCompilationFuel (.choice left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hWhole :
            compileTypeFuel signature (typeCompilationFuel (.choice left right))
              (.choice left right) =
              buildChoiceAutomaton signature
                (compileTypeFuel signature (typeCompilationFuel left) left)
                (compileTypeFuel signature (typeCompilationFuel right) right)
                TypeLabel.silent TypeLabel.silent := by
          rw [hFuelEq]
          show buildChoiceAutomaton signature
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              TypeLabel.silent TypeLabel.silent =
            buildChoiceAutomaton signature (compileTypeFuel signature
              (typeCompilationFuel left) left) (compileTypeFuel signature
              (typeCompilationFuel right) right) TypeLabel.silent TypeLabel.silent
          rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
        have hAcceptEq : (compileType signature (.choice left right)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature (typeCompilationFuel (.choice left right))
            (.choice left right)).accepting = _
          rw [hWhole]; simp [buildChoiceAutomaton, finishAutomatonFragment]
        rw [hAcceptEq]
        have hShape := helper_h12_binaryChoice_shape signature (.choice left right) left right
          rfl hFuelEq hRelated
        rcases hShape with ⟨hResidualEq, hStateEq⟩ |
          ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
        · subst hResidualEq; subst hStateEq
          simp [childAccepting, childState]
        · subst hStateEq
          simp only [childAccepting, Finset.mem_union, Finset.mem_image, childState]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨q', hq', hEq⟩)
            · injection hEq with _ hEq'
              exact (ih (sizeOf left) hLeftSize hLeftRelated rfl).mp (hEq' ▸ hq')
            · exact absurd hEq (by simp)
          · intro hSkip
            exact Or.inl ⟨q, (ih (sizeOf left) hLeftSize hLeftRelated rfl).mpr hSkip, rfl⟩
        · subst hStateEq
          simp only [childAccepting, Finset.mem_union, Finset.mem_image, childState]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨q', hq', hEq⟩)
            · exact absurd hEq (by simp)
            · injection hEq with _ hEq'
              exact (ih (sizeOf right) hRightSize hRightRelated rfl).mp (hEq' ▸ hq')
          · intro hSkip
            exact Or.inr ⟨q, (ih (sizeOf right) hRightSize hRightRelated rfl).mpr hSkip, rfl⟩
    | fairChoice bid left right =>
        have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
        have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
        have hFuelEq : typeCompilationFuel (.fairChoice bid left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hWhole :
            compileTypeFuel signature (typeCompilationFuel (.fairChoice bid left right))
              (.fairChoice bid left right) =
              buildChoiceAutomaton signature
                (compileTypeFuel signature (typeCompilationFuel left) left)
                (compileTypeFuel signature (typeCompilationFuel right) right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
          rw [hFuelEq]
          show buildChoiceAutomaton signature
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
            buildChoiceAutomaton signature (compileTypeFuel signature
              (typeCompilationFuel left) left) (compileTypeFuel signature
              (typeCompilationFuel right) right) (TypeLabel.fair bid true)
              (TypeLabel.fair bid false)
          rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
        have hAcceptEq : (compileType signature (.fairChoice bid left right)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature (typeCompilationFuel (.fairChoice bid left right))
            (.fairChoice bid left right)).accepting = _
          rw [hWhole]; simp [buildChoiceAutomaton, finishAutomatonFragment]
        rw [hAcceptEq]
        have hShape := helper_h12_binaryChoice_shape signature (.fairChoice bid left right)
          left right rfl hFuelEq hRelated
        rcases hShape with ⟨hResidualEq, hStateEq⟩ |
          ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
        · subst hResidualEq; subst hStateEq
          simp [childAccepting, childState]
        · subst hStateEq
          simp only [childAccepting, Finset.mem_union, Finset.mem_image, childState]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨q', hq', hEq⟩)
            · injection hEq with _ hEq'
              exact (ih (sizeOf left) hLeftSize hLeftRelated rfl).mp (hEq' ▸ hq')
            · exact absurd hEq (by simp)
          · intro hSkip
            exact Or.inl ⟨q, (ih (sizeOf left) hLeftSize hLeftRelated rfl).mpr hSkip, rfl⟩
        · subst hStateEq
          simp only [childAccepting, Finset.mem_union, Finset.mem_image, childState]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨q', hq', hEq⟩)
            · exact absurd hEq (by simp)
            · injection hEq with _ hEq'
              exact (ih (sizeOf right) hRightSize hRightRelated rfl).mp (hEq' ▸ hq')
          · intro hSkip
            exact Or.inr ⟨q, (ih (sizeOf right) hRightSize hRightRelated rfl).mpr hSkip, rfl⟩
    | recur name body =>
        have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
        have hFuelEq : typeCompilationFuel (.recur name body) = typeCompilationFuel body + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq : (compileType signature (.recur name body)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel body) body) := by
          show (compileTypeFuel signature (typeCompilationFuel (.recur name body))
            (.recur name body)).accepting = _
          rw [hFuelEq]
          show (buildRecursionAutomaton signature name
            (compileTypeFuel signature (typeCompilationFuel body) body)).accepting = _
          simp [buildRecursionAutomaton, finishAutomatonFragment]
        rw [hAcceptEq]
        have hMem : (residual, state) ∈
            buildRelationSetCoreFuel signature (typeCompilationFuel (.recur name body))
              (.recur name body) := hRelated
        rw [hFuelEq] at hMem
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image,
          Prod.mk.injEq] at hMem
        rcases hMem with ⟨hResidualEq, hStateEq⟩ | ⟨entry, hEntry, hR, hS⟩
        · subst hResidualEq; subst hStateEq
          simp [childAccepting, childState]
        · subst hS
          have hEntryRelated :
              relationMembership (buildRelationSet body (compileType signature body))
                entry.1 entry.2 := hEntry
          have hIH := ih (sizeOf body) hBodySize hEntryRelated rfl
          simp only [childAccepting, Finset.mem_image, childState]
          constructor
          · rintro ⟨q', hq', hEq⟩
            injection hEq with _ hEq'
            rw [← hR, replaceVar_eq_skip_iff entry.1 name (.recur name body) (by simp)]
            exact hIH.mp (hEq' ▸ hq')
          · intro hSkip
            rw [← hR, replaceVar_eq_skip_iff entry.1 name (.recur name body) (by simp)]
              at hSkip
            exact ⟨entry.2, hIH.mpr hSkip, rfl⟩
    | seq first second =>
        have hSecondSize : sizeOf second < n := by rw [← hSize]; simp_wf; omega
        exact helper_h13_seq_case signature first second
          (fun hR => ih (sizeOf second) hSecondSize hR rfl) hRelated
    | par left right interface =>
        exact helper_h13_par_case signature left right interface hRelated
    | xoffer elseType branches =>
        have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
        have hBranchesSize : ∀ branch ∈ branches, sizeOf branch.2 < n := by
          intro branch hBranch
          have hEntry : sizeOf branch < sizeOf branches := List.sizeOf_lt_of_mem hBranch
          have hComponent : sizeOf branch.2 < sizeOf branch := by
            obtain ⟨action, branchType⟩ := branch
            simp; omega
          rw [← hSize]; simp_wf; omega
        exact helper_h13_xoffer_case signature elseType branches
          (fun hR => ih (sizeOf elseType) hElseSize hR rfl)
          (by
            intro branch hBranch residual state hR
            exact ih (sizeOf branch.2) (hBranchesSize branch hBranch) hR rfl)
          hRelated
    | offer elseType branches =>
        have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
        have hBranchesSize : ∀ branch ∈ branches, sizeOf branch.2 < n := by
          intro branch hBranch
          have hEntry : sizeOf branch < sizeOf branches := List.sizeOf_lt_of_mem hBranch
          have hComponent : sizeOf branch.2 < sizeOf branch := by
            obtain ⟨action, branchType⟩ := branch
            simp; omega
          rw [← hSize]; simp_wf; omega
        have hBranchesH13 : ∀ branch ∈ branches, ∀ {residual : PactType}
            {state : TypeAutomatonState},
            relationMembership (buildRelationSet branch.2 (compileType signature branch.2))
              residual state →
            (state ∈ (compileType signature branch.2).accepting ↔ residual = .skip) := by
          intro branch hBranch residual state hR
          exact ih (sizeOf branch.2) (hBranchesSize branch hBranch) hR rfl
        have hFuelEq : typeCompilationFuel (.offer elseType branches) =
            max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq : (compileType signature (.offer elseType branches)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel elseType) elseType) ∪
              indexedFragmentAccepting (branches.map fun selected =>
                (selected.1, compileTypeFuel signature
                  (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
                  (parallelTypeBranchesSelecting selected branches))) := by
          show (compileTypeFuel signature (typeCompilationFuel (.offer elseType branches))
            (.offer elseType branches)).accepting = _
          rw [hFuelEq]
          show (buildSelectedConjunctiveOfferAutomaton signature branches
            (compileTypeFuel signature
              (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)) elseType)
            (branches.map fun selected => (selected.1, compileTypeFuel signature
              (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
              (parallelTypeBranchesSelecting selected branches)))).accepting = _
          rw [compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl]
          simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment]
          congr 2
          apply List.map_congr_left
          intro selected hSelected
          congr 1
          exact compileTypeFuel_eq_of_sufficient signature
            (parallelTypeBranchesSelecting selected branches)
            (by
              show typeCompilationFuel (parallelTypeBranchesSelecting selected branches) ≤ _
              rw [typeCompilationFuel_parallelTypeBranchesSelecting]
              exact le_max_right _ _)
            le_rfl
        rw [hAcceptEq]
        have hMem : (residual, state) ∈
            buildRelationSetCoreFuel signature (typeCompilationFuel (.offer elseType branches))
              (.offer elseType branches) := hRelated
        rw [hFuelEq] at hMem
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
          mem_foldl_union_iff, Finset.notMem_empty, false_or, Finset.mem_image,
          Prod.mk.injEq] at hMem
        rcases hMem with ⟨hResidualEq, hStateEq⟩ | ⟨a, ha, hR, hS⟩ |
          ⟨item, hItem, a, ha, hR, hS⟩
        · subst hResidualEq; subst hStateEq
          simp [childAccepting, childState, indexedFragmentAccepting, mem_foldl_union_iff]
        · subst hR; subst hS
          have hEntryRelated :
              relationMembership (buildRelationSet elseType (compileType signature elseType))
                a.1 a.2 := by
            show (a.1, a.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel elseType)
              elseType
            rw [← buildRelationSetCoreFuel_eq_of_sufficient signature elseType
              (le_max_left _ _) le_rfl]
            exact ha
          have hIH := ih (sizeOf elseType) hElseSize hEntryRelated rfl
          simp only [Finset.mem_union, childAccepting, Finset.mem_image, childState,
            indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨item', hItem', q', -, hEq⟩)
            · injection hEq with _ hEq'
              exact hIH.mp (hEq' ▸ hq')
            · exact nomatch hEq
          · intro hSkip
            exact Or.inl ⟨a.2, hIH.mpr hSkip, rfl⟩
        · subst hR; subst hS
          have hMemBranches : item.1 ∈ branches := by
            have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
            exact List.mem_of_getElem? hGet
          have hItemFuel : typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches) ≤
              max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) := by
            rw [typeCompilationFuel_parallelTypeBranchesSelecting]
            exact le_max_right _ _
          have hEntryRelated :
              relationMembership
                (buildRelationSet (parallelTypeBranchesSelecting item.1 branches)
                  (compileType signature (parallelTypeBranchesSelecting item.1 branches)))
                a.1 a.2 := by
            show (a.1, a.2) ∈ buildRelationSetCoreFuel signature
              (typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches))
              (parallelTypeBranchesSelecting item.1 branches)
            rw [← buildRelationSetCoreFuel_eq_of_sufficient signature
              (parallelTypeBranchesSelecting item.1 branches) hItemFuel le_rfl]
            exact ha
          have hIH := helper_h13_parallelTypeBranchesSelecting signature item.1 branches
            hBranchesH13 hEntryRelated
          have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
          have hMapGet :
              (branches.map fun selected => (selected.1, compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
                (parallelTypeBranchesSelecting selected branches)))[item.2]? =
                some (item.1.1, compileTypeFuel signature
                  (typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches))
                  (parallelTypeBranchesSelecting item.1 branches)) := by
            rw [List.getElem?_map, hGet]; rfl
          simp only [Finset.mem_union, childAccepting, Finset.mem_image, childState,
            indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
          constructor
          · rintro (⟨q1, hq1, hEq1⟩ | ⟨item', hItem', q2, hq2, hEq2⟩)
            · exact nomatch hEq1
            · injection hEq2 with hIdxEq hQEq
              have hItemEq : item'.1 = (item.1.1, compileTypeFuel signature
                  (typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches))
                  (parallelTypeBranchesSelecting item.1 branches)) := by
                have hGet' := List.mk_mem_zipIdx_iff_getElem?.mp hItem'
                have hIdxEq' : item'.2 = item.2 := by omega
                rw [hIdxEq'] at hGet'
                rw [hMapGet] at hGet'
                injection hGet' with hFst
                exact hFst.symm
              rw [hItemEq] at hq2
              exact hIH.mp (hQEq ▸ hq2)
          · intro hSkip
            refine Or.inr ⟨((item.1.1, compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches))
                (parallelTypeBranchesSelecting item.1 branches)), item.2),
              List.mk_mem_zipIdx_iff_getElem?.mpr hMapGet, a.2, hIH.mpr hSkip, rfl⟩

/-- Helper Lemma H15, edge form: a public edge carries the target menu after removing its current offer. -/
lemma helper_h15_edge_future_offers_agree
    (signature : TypeAlphabet) {processType residual residual' : PactType}
    {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual source)
    (hTarget :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual' target)
    (hEdge :
      (compileType signature processType).HasEdge source env label
        (TypeOfferSummary.mk current future) target) :
    future = typeFutureOffers residual' \ current := by
  sorry -- TODO(section7): derive from global future agreement and edge resolution.

end

end Pact
