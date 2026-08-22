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

/-- Helper Lemma H12: related compiled states are states of the compiled
automaton. -/
lemma helper_h12_compiled_state_shape
    (signature : TypeAlphabet) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual state) :
    state ∈ (compileType signature processType).states := by
  -- Now prove the builder invariant: the seed is a state, and edge targets stay states.
  let automaton := compileType signature processType
  change (residual, state).2 ∈ automaton.states
  exact buildRelationSet_preserves processType automaton
    (fun entry => entry.2 ∈ automaton.states)
    (by
      dsimp [automaton]
      simpa using compileType_initial_mem signature processType)
    (by
      intro entry _hEntry successor hSuccessor
      rcases relationSuccessors_mem_cases automaton entry successor hSuccessor
        with ⟨edge, hEdge, hSource, hTarget, _hStep⟩
      rcases edge with ⟨edgeSource, ⟨edgeEnv, edgeLabel, edgeOffers⟩,
        edgeTarget⟩
      have hPublicEdge :
          (compileType signature processType).HasEdge edgeSource edgeEnv
            edgeLabel edgeOffers edgeTarget := by
        simpa [automaton, TypeAutomaton.HasEdge] using hEdge
      have hTargetMem :
          edgeTarget ∈ (compileType signature processType).states :=
        compileType_edge_target_mem signature processType hPublicEdge
      simpa [automaton, hTarget] using hTargetMem)
    (residual, state) hRelated

/-- Helper Lemma H15: future offers agree. Moved ahead of the H13 section
below (from its original position after H13) since H13's `.choice`/
`.fairChoice` cases cite it — Lean needs the forward declaration. -/
lemma helper_h15_future_offers_agree
    (signature : TypeAlphabet) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual state) :
    computeFutureOf signature processType state = typeFutureOffers residual := by
  sorry -- TODO(section7): prove by the constructor future-correctness bundle.

/-! ### Helper Lemma H13: final states represent completion

Proved directly by induction on the compilation rule, exactly as `pact.pdf`
structures it ("We prove both directions by induction on the compilation
rule"): one theorem, `helper_h13_final_states_represent_completion` below,
case-split on `processType`'s constructor, each case citing Helper Lemma
H12 (the shape of the represented residual, per compilation rule) and the
child induction hypothesis, matching the paper's own brevity. Lean's
`induction` tactic doesn't support `PactType` directly (it has a nested
`List (BareMessage × PactType)` field, so it's a nested inductive type),
so the induction is phrased as `Nat.strong_induction_on (sizeOf
processType)`, exactly as `correspondence_stepIff` (`CasesTop.lean`)
already does — the same underlying induction, in the encoding Lean needs. -/

/-- A decorated type step's target is uniquely determined by its source,
environment, label, and offers. This mirrors the identically-named,
identically-`sorry`'d fact tracked as `decoratedTypeTransition_target_unique`
in `PactTypes.NewCorrespondence.Helpers.lean` — a separate, concurrently-developed
file this development does not touch, so this local copy carries the same
still-open general `TypeTransition` determinism gap under its own name. -/
theorem H13_decoratedTypeTransition_target_unique
    {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
    {offers : TypeOfferSummary} {target target' : PactType}
    (hStep : DecoratedTypeTransition env source label offers target)
    (hStep' : DecoratedTypeTransition env source label offers target') :
    target = target' := by
  sorry -- TODO(section7): general TypeTransition determinism, tracked jointly with
  -- `decoratedTypeTransition_target_unique` (PactTypes.NewCorrespondence.Helpers.lean).

/-- Every local environment a signature generates is well-formed. Local copy
of `localEnvironment_wellFormed` (`PactTypes.NewCorrespondence.Helpers.lean`) — that
one's proof is fully self-contained (unfolds only `TypeAlphabet.localEnvironments`
and generic `Finset` facts, both upstream of `ProofHelpers.lean`), so
it's reproduced verbatim here under a distinct name rather than imported. -/
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

/-- A `.child 0`-tagged state's future menu, in a compiled binary choice,
agrees with the left child's own. Mirrors the identically-`sorry`'d
`computeFutureOf_binaryChoice_left` (`PactTypes.NewCorrespondence.Helpers.lean`,
itself not yet proven either) — needs `ReferencesClosed`/state-count
preconditions not established anywhere upstream of `ProofHelpers.lean`,
so this local copy carries the same open gap under its own name. -/
theorem H13_computeFutureOf_binaryChoice_left
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState) :
    computeFutureOf signature whole (.child 0 state) =
      computeFutureOf signature left state := by
  sorry -- TODO(section7): shared computeFutureOf-transport gap, see doc comment.

/-- A `.child 1`-tagged state's future menu, in a compiled binary choice,
agrees with the right child's own. See `H13_computeFutureOf_binaryChoice_left`. -/
theorem H13_computeFutureOf_binaryChoice_right
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel right + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState) :
    computeFutureOf signature whole (.child 1 state) =
      computeFutureOf signature right state := by
  sorry -- TODO(section7): shared computeFutureOf-transport gap, see doc comment.

set_option maxHeartbeats 4000000 in
/-- Helper Lemma H12, binary choice case: a fresh root represents the whole
choice, and a child-tagged state represents whatever its own child relates
it to. Shared between `.choice` and `.fairChoice`, generic over the two
selection labels — the caller supplies how to resolve the label ambiguity
at the root (`hRootLeft`/`hRootRight`): `.choice` needs determinism (its two
labels coincide), `.fairChoice` doesn't (its two labels are syntactically
distinct, so `cases` on the semantic step alone already disambiguates). -/
theorem helper_h12_binaryChoice_shape
    (signature : TypeAlphabet) (whole left right : PactType)
    (label1 label2 : TypeLabel)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          label1 label2)
    (hFuelLeft : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole)
    (hFuelRight : typeCompilationFuel right + 1 ≤ typeCompilationFuel whole)
    (hRootLeft :
      ∀ {env : TypeEnvironment} {target : PactType}, env.WellFormed →
        DecoratedTypeTransition env whole label1
          (TypeOfferSummary.mk ∅ (typeFutureOffers left)) target → target = left)
    (hRootRight :
      ∀ {env : TypeEnvironment} {target : PactType}, env.WellFormed →
        DecoratedTypeTransition env whole label2
          (TypeOfferSummary.mk ∅ (typeFutureOffers right)) target → target = right)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet whole (compileType signature whole))
        residual state) :
    (residual = whole ∧ state = TypeAutomatonState.root) ∨
    (∃ q1, state = .child 0 q1 ∧
      relationMembership (buildRelationSet left (compileType signature left)) residual q1) ∨
    (∃ q2, state = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType signature right)) residual q2) := by
  have hInitEq : (compileType signature whole).initial = TypeAutomatonState.root := by
    show (compileTypeFuel signature (typeCompilationFuel whole) whole).initial = _
    rw [hWhole]; simp [buildChoiceAutomaton, finishAutomatonFragment]
  have hFutureLeftEq : computeFutureOf signature whole
      (.child 0 (compileTypeFuel signature (typeCompilationFuel left) left).initial) =
      typeFutureOffers left := by
    rw [H13_computeFutureOf_binaryChoice_left signature left right label1 label2 whole
      hWhole hFuelLeft (compileTypeFuel signature (typeCompilationFuel left) left).initial]
    show computeFutureOf signature left (compileType signature left).initial =
      typeFutureOffers left
    exact helper_h15_future_offers_agree signature
      (buildRelationSet_initial left (compileType signature left))
  have hFutureRightEq : computeFutureOf signature whole
      (.child 1 (compileTypeFuel signature (typeCompilationFuel right) right).initial) =
      typeFutureOffers right := by
    rw [H13_computeFutureOf_binaryChoice_right signature left right label1 label2 whole
      hWhole hFuelRight (compileTypeFuel signature (typeCompilationFuel right) right).initial]
    show computeFutureOf signature right (compileType signature right).initial =
      typeFutureOffers right
    exact helper_h15_future_offers_agree signature
      (buildRelationSet_initial right (compileType signature right))
  have hResult :=
    buildRelationSet_preserves whole (compileType signature whole)
      (fun entry =>
        (entry.1 = whole ∧ entry.2 = TypeAutomatonState.root) ∨
        (∃ q1, entry.2 = .child 0 q1 ∧
          relationMembership (buildRelationSet left (compileType signature left)) entry.1 q1) ∨
        (∃ q2, entry.2 = .child 1 q2 ∧
          relationMembership (buildRelationSet right (compileType signature right)) entry.1 q2))
      (by rw [hInitEq]; exact Or.inl ⟨rfl, rfl⟩)
      (by
        intro entry hEntry successor hSuccessor
        rcases relationSuccessors_mem_cases (compileType signature whole) entry successor
          hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
        have hPublicEdge :
            (compileType signature whole).HasEdge entry.2 edge.symbol.environment
              edge.symbol.label edge.symbol.offers successor.2 := by
          rw [← hSource, hTarget]; exact hEdgeMem
        have hSymbol := NewCorrespondence.compileType_hasEdge_symbol_mem signature whole
          hPublicEdge
        have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature whole entry.2
          successor.2 edge.symbol.environment edge.symbol.label edge.symbol.offers
          hSymbol).mp hPublicEdge
        rw [hWhole] at hResolved
        obtain ⟨pendingEdge, hMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
          hPTarget⟩ := hResolved
        simp only [buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
          Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
          Finset.mem_singleton] at hMem
        rcases hEntry with ⟨hResidualEq, hStateEq⟩ |
          ⟨q1, hStateEq, hLeftRelated⟩ | ⟨q2, hStateEq, hRightRelated⟩
        · -- entry is the root: the fired edge must be a selection edge.
          rw [hStateEq] at hPSource
          rcases hMem with (hLeft | hRight) | hSelection
          · obtain ⟨childEdge, -, hEq⟩ := hLeft
            rw [← hEq] at hPSource; simp [childPendingEdge, childState] at hPSource
          · obtain ⟨childEdge, -, hEq⟩ := hRight
            rw [← hEq] at hPSource; simp [childPendingEdge, childState] at hPSource
          · obtain ⟨environment, -, hEq | hEq⟩ := hSelection
            · rw [hEq] at hPLabel hPTarget hPCurrent hPFuture
              simp only at hPLabel hPTarget hPCurrent hPFuture
              have hFutureEq : edge.symbol.offers.future = typeFutureOffers left := by
                rw [← hPFuture, Finset.sdiff_empty]; exact hFutureLeftEq
              have hOffersEq : edge.symbol.offers =
                  TypeOfferSummary.mk ∅ (typeFutureOffers left) := by
                rw [show edge.symbol.offers =
                  TypeOfferSummary.mk edge.symbol.offers.current edge.symbol.offers.future
                  from rfl, hFutureEq, ← hPCurrent]
              have hLabelEq : label1 = edge.symbol.label := by injection hPLabel
              rw [hResidualEq, ← hLabelEq, hOffersEq] at hStep
              have hWF : edge.symbol.environment.WellFormed :=
                H13_localEnvironment_wellFormed signature
                  (TypeAlphabet.environments_subset_localEnvironments signature
                    (NewCorrespondence.transitionAlphabet_environment_mem signature hSymbol))
              have hTargetEq : successor.1 = left := hRootLeft hWF hStep
              have hStateEq' : successor.2 = .child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial :=
                hPTarget.symm
              exact Or.inr (Or.inl ⟨(compileTypeFuel signature (typeCompilationFuel left)
                left).initial, hStateEq', hTargetEq ▸
                buildRelationSet_initial left (compileType signature left)⟩)
            · rw [hEq] at hPLabel hPTarget hPCurrent hPFuture
              simp only at hPLabel hPTarget hPCurrent hPFuture
              have hFutureEq : edge.symbol.offers.future = typeFutureOffers right := by
                rw [← hPFuture, Finset.sdiff_empty]; exact hFutureRightEq
              have hOffersEq : edge.symbol.offers =
                  TypeOfferSummary.mk ∅ (typeFutureOffers right) := by
                rw [show edge.symbol.offers =
                  TypeOfferSummary.mk edge.symbol.offers.current edge.symbol.offers.future
                  from rfl, hFutureEq, ← hPCurrent]
              have hLabelEq : label2 = edge.symbol.label := by injection hPLabel
              rw [hResidualEq, ← hLabelEq, hOffersEq] at hStep
              have hWF : edge.symbol.environment.WellFormed :=
                H13_localEnvironment_wellFormed signature
                  (TypeAlphabet.environments_subset_localEnvironments signature
                    (NewCorrespondence.transitionAlphabet_environment_mem signature hSymbol))
              have hTargetEq : successor.1 = right := hRootRight hWF hStep
              have hStateEq' : successor.2 = .child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial :=
                hPTarget.symm
              exact Or.inr (Or.inr ⟨(compileTypeFuel signature (typeCompilationFuel right)
                right).initial, hStateEq', hTargetEq ▸
                buildRelationSet_initial right (compileType signature right)⟩)
        · -- entry is a left-tagged state: the fired edge stays inside left.
          rw [hStateEq] at hPSource
          rcases hMem with (hLeft | hRight) | hSelection
          · obtain ⟨childEdge, hChildEdgeMem, hEq⟩ := hLeft
            have hChildSource : childEdge.source = q1 := by
              have h := hPSource; rw [← hEq] at h; simpa [childPendingEdge, childState] using h
            have hInnerEdge :
                (compileType signature left).HasEdge q1 edge.symbol.environment
                  edge.symbol.label edge.symbol.offers childEdge.target := by
              rw [compileType_hasEdge_iff_hasResolvedEdge signature left q1 childEdge.target
                edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbol]
              refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
              · rw [← hPEnv, ← hEq]; rfl
              · rw [← hPLabel, ← hEq]; rfl
              · rw [← hPCurrent, ← hEq]; rfl
              · rw [← hPFuture, ← hEq]
                cases hSpec : childEdge.future with
                | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
                | «at» futureState removed =>
                    simp only [childPendingEdge, childFutureSpec, hSpec, childState]
                    exact H13_computeFutureOf_binaryChoice_left signature left right label1
                      label2 whole hWhole hFuelLeft futureState ▸ rfl
            exact Or.inr (Or.inl ⟨childEdge.target,
              by rw [← hPTarget, ← hEq]; rfl,
              relationMembership_of_step_edge_unique left (compileType signature left)
                hLeftRelated hInnerEdge hStep
                (fun target hTargetStep =>
                  H13_decoratedTypeTransition_target_unique hTargetStep hStep)⟩)
          · obtain ⟨childEdge, -, hEq⟩ := hRight
            rw [← hEq] at hPSource; simp [childPendingEdge, childState] at hPSource
          · obtain ⟨environment, -, hEq | hEq⟩ := hSelection <;>
              (rw [hEq] at hPSource; simp at hPSource)
        · -- entry is a right-tagged state: the fired edge stays inside right.
          rw [hStateEq] at hPSource
          rcases hMem with (hLeft | hRight) | hSelection
          · obtain ⟨childEdge, -, hEq⟩ := hLeft
            rw [← hEq] at hPSource; simp [childPendingEdge, childState] at hPSource
          · obtain ⟨childEdge, hChildEdgeMem, hEq⟩ := hRight
            have hChildSource : childEdge.source = q2 := by
              have h := hPSource; rw [← hEq] at h; simpa [childPendingEdge, childState] using h
            have hInnerEdge :
                (compileType signature right).HasEdge q2 edge.symbol.environment
                  edge.symbol.label edge.symbol.offers childEdge.target := by
              rw [compileType_hasEdge_iff_hasResolvedEdge signature right q2 childEdge.target
                edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbol]
              refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
              · rw [← hPEnv, ← hEq]; rfl
              · rw [← hPLabel, ← hEq]; rfl
              · rw [← hPCurrent, ← hEq]; rfl
              · rw [← hPFuture, ← hEq]
                cases hSpec : childEdge.future with
                | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
                | «at» futureState removed =>
                    simp only [childPendingEdge, childFutureSpec, hSpec, childState]
                    exact H13_computeFutureOf_binaryChoice_right signature left right label1
                      label2 whole hWhole hFuelRight futureState ▸ rfl
            exact Or.inr (Or.inr ⟨childEdge.target,
              by rw [← hPTarget, ← hEq]; rfl,
              relationMembership_of_step_edge_unique right (compileType signature right)
                hRightRelated hInnerEdge hStep
                (fun target hTargetStep =>
                  H13_decoratedTypeTransition_target_unique hTargetStep hStep)⟩)
          · obtain ⟨environment, -, hEq | hEq⟩ := hSelection <;>
              (rw [hEq] at hPSource; simp at hPSource))
  exact hResult (residual, state) hRelated

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

/-- Helper Lemma H13: final states represent completion. Proved directly by
induction on the compilation rule (`Nat.strong_induction_on (sizeOf
processType)`, the encoding Lean's nested-inductive `PactType` needs — see
the section comment above). The atomic cases and the open-variable case are
immediate. `choice`/`fairChoice` cite Helper Lemma H12
(`helper_h12_binaryChoice_shape`) and the child hypothesis. `recur`, `seq`,
`par`, and the two offer constructors are deferred (see the `sorry`s below):
each needs its own from-scratch edge-inversion, mirroring the choice/fairChoice
argument's shape but against a different compiled-automaton construction. -/
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
        have hEdgesEmpty := compileType_var_edges_empty signature name
        have hShape :
            ∀ entry ∈ buildRelationSet (.var name) (compileType signature (.var name)),
              entry = (PactType.var name, TypeAutomatonState.root) :=
          buildRelationSet_preserves (.var name) (compileType signature (.var name))
            (fun entry => entry = (PactType.var name, TypeAutomatonState.root))
            (by simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment])
            (by
              intro entry _hEntry successor hSuccessor
              exfalso
              unfold relationSuccessors at hSuccessor
              rw [hEdgesEmpty] at hSuccessor
              simp at hSuccessor)
        have hEq := hShape (residual, state) hRelated
        injection hEq with hResidualEq hStateEq
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
        have hFuelLeft : typeCompilationFuel left + 1 ≤ typeCompilationFuel (.choice left right) := by
          simp only [typeCompilationFuel]; omega
        have hFuelRight : typeCompilationFuel right + 1 ≤
            typeCompilationFuel (.choice left right) := by
          simp only [typeCompilationFuel]; omega
        have hShape := helper_h12_binaryChoice_shape signature (.choice left right) left right
          TypeLabel.silent TypeLabel.silent hWhole hFuelLeft hFuelRight
          (fun {env target} hWF hStep' =>
            H13_decoratedTypeTransition_target_unique hStep'
              ⟨TypeTransition.choice_left env left right hWF,
                TypeOffers.choice_left env left right hWF⟩)
          (fun {env target} hWF hStep' =>
            H13_decoratedTypeTransition_target_unique hStep'
              ⟨TypeTransition.choice_right env left right hWF,
                TypeOffers.choice_right env left right hWF⟩)
          hRelated
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
        have hFuelLeft : typeCompilationFuel left + 1 ≤
            typeCompilationFuel (.fairChoice bid left right) := by
          simp only [typeCompilationFuel]; omega
        have hFuelRight : typeCompilationFuel right + 1 ≤
            typeCompilationFuel (.fairChoice bid left right) := by
          simp only [typeCompilationFuel]; omega
        have hShape := helper_h12_binaryChoice_shape signature (.fairChoice bid left right)
          left right (TypeLabel.fair bid true) (TypeLabel.fair bid false) hWhole hFuelLeft
          hFuelRight
          (fun {env target} _hWF hStep' => by
            obtain ⟨hTrans, -⟩ := hStep'
            generalize hL : TypeLabel.fair bid true = actualLabel at hTrans
            cases hTrans with
            | fair_left => rfl
            | fair_right => exact absurd hL (by simp [TypeLabel.fair, Finset.ext_iff]))
          (fun {env target} _hWF hStep' => by
            obtain ⟨hTrans, -⟩ := hStep'
            generalize hL : TypeLabel.fair bid false = actualLabel at hTrans
            cases hTrans with
            | fair_left => exact absurd hL (by simp [TypeLabel.fair, Finset.ext_iff])
            | fair_right => rfl)
          hRelated
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
        sorry -- TODO(section7): H13, `recur` case — needs its own edge-inversion,
        -- mirroring `helper_h12_binaryChoice_shape`'s argument against
        -- `buildRecursionAutomaton`'s header/tagged-body/marker edge families.
    | seq first second =>
        sorry -- TODO(section7): H13, `seq` case — needs `buildSequenceAutomaton`'s own
        -- redirect/entry-bridge edge-inversion, rebuilt from scratch (the existing
        -- `buildSequenceAutomaton_outgoing_left_visible` lives in the off-limits file).
    | par left right interface =>
        sorry -- TODO(section7): H13, `par` case — needs `buildParallelAutomaton`'s own
        -- synchronized-product edge-inversion, rebuilt from scratch.
    | xoffer elseType branches =>
        sorry -- TODO(section7): H13, `xoffer` case — list-indexed branches, likely the
        -- hardest remaining case; needs its own finite-branch induction like
        -- `correspondence_xoffer_stepIff`'s.
    | offer elseType branches =>
        sorry -- TODO(section7): H13, `offer` case — as `xoffer`, plus needs H13 for the
        -- generated `parallelTypeBranchesSelecting` commit type via its own
        -- finite-branch induction (mirroring `correspondence_parallelTypeBranches_stepIff`).

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
