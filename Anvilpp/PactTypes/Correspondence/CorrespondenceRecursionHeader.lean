import Anvilpp.PactTypes.Correspondence.CorrespondenceCompleting

/-!
# Recursion header and closed recursion-fragment correspondence
-/

namespace Pact

noncomputable section

/-! ### Recursion header correspondence -/

/-- The graph-future equality used to decorate the explicit silent edge from
a recursion binder header into its body.  The semantic target is the usual
capture-avoiding unfolding of the body. -/
def RecursionHeaderFutureCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let fragment := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  computeFuture pending (.child 0 bodyFragment.initial) =
    typeFutureOffers (body.replaceVar name (.recur name body))

/-- The recursion binder's explicit header edge is present with the exact
decoration of the unfolded body. -/
theorem compileType_recursion_header_edge
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : RecursionHeaderFutureCorrect signature name body)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅
        (typeFutureOffers (body.replaceVar name (.recur name body)))) ∈
          signature.transitionAlphabet) :
    (compileType signature (.recur name body)).HasEdge .root env
      TypeLabel.silent
      (TypeOfferSummary.mk ∅
        (typeFutureOffers (body.replaceVar name (.recur name body))))
      (.child 0 (compileType signature body).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let fragment := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 0 bodyFragment.initial) =
        typeFutureOffers (body.replaceVar name (.recur name body)) := by
    simpa [pending, fragment, bodyFragment] using hFuture
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.recur name body))
          (.recur name body) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := typeFutureOffers (body.replaceVar name (.recur name body))
      target := .child 0 bodyFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 0 bodyFragment.initial) ∅
        target := .child 0 bodyFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      simp [fragment, buildRecursionAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      left
      rfl
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, bodyFragment]

/-- Complete root-state correspondence for the explicit recursion-unfolding
step. -/
theorem compileType_recursion_header_step_iff
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : RecursionHeaderFutureCorrect signature name body)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅
        (typeFutureOffers (body.replaceVar name (.recur name body)))) ∈
          signature.transitionAlphabet) :
    DecoratedTypeTransition env (.recur name body) TypeLabel.silent
        (TypeOfferSummary.mk ∅
          (typeFutureOffers (body.replaceVar name (.recur name body))))
        (body.replaceVar name (.recur name body)) ↔
      ∃ state',
        (compileType signature (.recur name body)).HasEdge .root env
            TypeLabel.silent
            (TypeOfferSummary.mk ∅
              (typeFutureOffers (body.replaceVar name (.recur name body))))
            state' ∧
          TypeCompilationRelation (.recur name body) state'
            (body.replaceVar name (.recur name body)) := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 0 (compileType signature body).initial, ?_, ?_⟩
    · exact compileType_recursion_header_edge signature name body
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.recur_body name body body _
        (compileType_initial_relation signature body)
  · intro _
    exact ⟨TypeTransition.recur env name body hWellFormed,
      TypeOffers.recur env name body hWellFormed⟩

/-! ### Closed recursion-fragment correspondence -/

/-- Exact classifier for resolved edges leaving the fresh recursion header,
before the public alphabet filter. -/
theorem buildRecursionAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (target : TypeAutomatonState) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    recursion.HasResolvedEdge .root env label offers target ↔
      env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (.child 0 body.initial) = offers.future ∧
        target = .child 0 body.initial := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge, buildRecursionAutomaton,
    finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    rcases hEdge with hHeader | hBody
    · rcases hHeader with ⟨edgeEnvironment, hLocal, rfl⟩
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      aesop
    · rcases hBody with ⟨bodyEdge, hBodyEdge, rfl⟩
      by_cases hVariable : bodyEdge.label = .variable name
      · simp [hVariable, childState] at hSource
      · simp [hVariable, childState] at hSource
  · rintro ⟨hLocal, rfl, hCurrent, hFuture, rfl⟩
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 0 body.initial) ∅
        target := .child 0 body.initial }, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · left
      exact ⟨env, hLocal, rfl⟩
    · exact hCurrent.symm
    · simpa using hFuture

/-- A matching variable marker in the body is installed as a silent backedge
to the tagged body entry, and is resolved only in the closed recursion graph. -/
theorem buildRecursionAutomaton_variable_marker_hasResolvedEdge
    (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ body.edges)
    (hVariable : edge.label = .variable name) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    recursion.HasResolvedEdge (.child 0 edge.source) edge.environment
      TypeLabel.silent
      { current := ∅,
        future := computeFuture pending (.child 0 body.initial) }
      (.child 0 body.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge]
  refine ⟨
    { source := .child 0 edge.source
      environment := edge.environment
      label := .visible TypeLabel.silent
      current := ∅
      future := .at (.child 0 body.initial) ∅
      target := .child 0 body.initial }, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [buildRecursionAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image]
    right
    refine ⟨edge, hEdge, ?_⟩
    simp [hVariable, childState]
  · simp

/-- Every resolved edge from a tagged recursion-body state is either the
installed matching-variable backedge or an unchanged non-matching body edge.
The latter's symbolic future is resolved in the enclosing recursion graph. -/
theorem buildRecursionAutomaton_body_hasResolvedEdge_iff
    (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) (source : TypeAutomatonState)
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    recursion.HasResolvedEdge (.child 0 source) env label offers target ↔
      (∃ edge ∈ body.edges,
        edge.source = source ∧ edge.label = .variable name ∧
          edge.environment = env ∧ label = TypeLabel.silent ∧
          offers.current = ∅ ∧
          computeFuture pending (.child 0 body.initial) = offers.future ∧
          target = .child 0 body.initial) ∨
      (∃ edge ∈ body.edges,
        edge.source = source ∧ edge.label ≠ .variable name ∧
          edge.environment = env ∧ edge.label = .visible label ∧
          edge.current = offers.current ∧
          (match edge.future with
            | .explicit future => future
            | .at state removed =>
                computeFuture pending (.child 0 state) \ removed) =
              offers.future ∧
          target = .child 0 edge.target) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge, buildRecursionAutomaton,
    finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨lifted, hLifted, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    rcases hLifted with hHeader | hBody
    · rcases hHeader with ⟨headerEnvironment, hLocal, rfl⟩
      simp at hSource
    · rcases hBody with ⟨edge, hEdge, rfl⟩
      by_cases hVariable : edge.label = .variable name
      · simp only [hVariable, if_true, Finset.sdiff_empty, childState]
          at hSource hEnvironment hLabel hCurrent hFuture hTarget
        have hEdgeSource : edge.source = source := by
          injection hSource
        have hVisibleLabel : label = TypeLabel.silent := by
          injection hLabel with hEquality
          exact hEquality.symm
        left
        exact ⟨edge, hEdge, hEdgeSource, hVariable, hEnvironment,
          hVisibleLabel, hCurrent.symm, hFuture, hTarget.symm⟩
      · simp only [hVariable, if_false, childState]
          at hSource hEnvironment hLabel hCurrent hTarget
        have hEdgeSource : edge.source = source := by
          injection hSource
        have hEdgeTarget : target = .child 0 edge.target := hTarget.symm
        right
        refine ⟨edge, hEdge, hEdgeSource, hVariable, hEnvironment,
          hLabel, hCurrent, ?_, hEdgeTarget⟩
        cases hSpec : edge.future with
        | explicit future =>
            simpa [hVariable, hSpec, childFutureSpec] using hFuture
        | «at» state removed =>
            simpa [hVariable, hSpec, childFutureSpec, childState]
              using hFuture
  · rintro (hMarker | hBody)
    · rcases hMarker with ⟨edge, hEdge, hSource, hVariable,
        hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .child 0 edge.source
          environment := edge.environment
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (.child 0 body.initial) ∅
          target := .child 0 body.initial }, ?_, ?_, hEnvironment, ?_,
            hCurrent.symm, ?_, hTarget.symm⟩
      · right
        refine ⟨edge, hEdge, ?_⟩
        simp [hVariable, childState]
      · simpa [hSource]
      · simpa [hLabel]
      · simpa using hFuture
    · rcases hBody with ⟨edge, hEdge, hSource, hVariable,
        hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .child 0 edge.source
          environment := edge.environment
          label := edge.label
          current := edge.current
          future := childFutureSpec 0 edge.future
          target := .child 0 edge.target }, ?_, ?_, hEnvironment,
            hLabel, hCurrent, ?_, ?_⟩
      · right
        exact ⟨edge, hEdge, by simp [hVariable, childState]⟩
      · simpa [hSource, childState]
      · cases hSpec : edge.future with
        | explicit future =>
            simpa [hSpec, childFutureSpec] using hFuture
        | «at» state removed =>
            simpa [hSpec, childFutureSpec, childState] using hFuture
      · simpa [hTarget, childState]

/-- Ambient syntax-future invariant required by recursion.  The left side is
computed in the closed binder graph, while the right side remains the
syntax-derived future menu of the unfolded residual. -/
def RecursionBodyFutureCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let recursion := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := recursion.states, edges := recursion.edges }
  ∀ state residual,
    TypeCompilationRelation body state residual →
      computeFuture pending (.child 0 state) =
        typeFutureOffers (residual.replaceVar name (.recur name body))

/-- The fresh recursion header contributes no offers of its own and has one
same-cycle reference, to the tagged body entry. -/
private theorem buildRecursionAutomaton_computeFuture_root
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hBodyTargets : body.FutureTargetsInStates)
    (hBodyInitial : body.initial ∈ body.states) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    computeFuture pending .root =
      computeFuture pending (.child 0 body.initial) := by
  classical
  let recursion := buildRecursionAutomaton signature name body
  let pending : PendingAutomaton :=
    { states := recursion.states, edges := recursion.edges }
  have hClosed : pending.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates recursion
    exact buildRecursionAutomaton_futureTargetsInStates signature name body
      hBodyTargets hBodyInitial
  have hRoot : (.root : TypeAutomatonState) ∈ pending.states := by
    simp [pending, recursion, buildRecursionAutomaton,
      finishAutomatonFragment]
  have hOffers : pending.offersAt .root = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [pending, recursion, buildRecursionAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with hHeader | hBody
    · rcases hHeader with ⟨environment, _, rfl⟩
      simp [AutomatonConstructionLabel.semantic] at hOffer
    · rcases hBody with ⟨bodyEdge, _, rfl⟩
      by_cases hVariable : bodyEdge.label = .variable name
      · simp [hVariable, childState] at hSource
      · simp [hVariable, childState] at hSource
  have hReferences : pending.referencedStates .root =
      {.child 0 body.initial} := by
    ext state
    constructor
    · intro hState
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter] at hState
      rcases hState with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
      simp only [pending, recursion, buildRecursionAutomaton,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image] at hEdge
      rcases hEdge with hHeader | hBody
      · rcases hHeader with ⟨environment, _, rfl⟩
        simp [AutomatonConstructionLabel.semantic] at hReference
        simpa [TypeLabel.silent] using hReference
      · rcases hBody with ⟨bodyEdge, _, rfl⟩
        by_cases hVariable : bodyEdge.label = .variable name
        · simp [hVariable, childState] at hSource
        · simp [hVariable, childState] at hSource
    · intro hState
      simp only [Finset.mem_singleton] at hState
      subst state
      let edge : PendingAutomatonEdge :=
        { source := .root
          environment := TypeEnvironment.tock
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (.child 0 body.initial) ∅
          target := .child 0 body.initial }
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter]
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [pending, recursion, buildRecursionAutomaton,
          finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
        left
        exact ⟨TypeEnvironment.tock,
          by simp [TypeAlphabet.localEnvironments], rfl⟩
      · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
  change computeFuture pending .root =
    computeFuture pending (.child 0 body.initial)
  rw [computeFuture_unfold pending .root hClosed hRoot, hOffers, hReferences]
  simp

/-- Whole-fragment future correctness supplies the ambient tagged-body
invariant required by the recursion constructor. -/
theorem recursionBodyFutureCorrect_of_compilationFutureCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : CompilationFutureCorrect signature (.recur name body)) :
    RecursionBodyFutureCorrect signature name body := by
  intro state residual hRelated
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
    hFuture (.child 0 state)
      (residual.replaceVar name (.recur name body))
      (TypeCompilationRelation.recur_body name body residual state hRelated)

/-- A clock-guarded binder's whole-fragment future correctness follows from
the closed tagged-body invariant.  The semantic menu on the right remains
the syntax-derived `typeFutureOffers`; the graph is used only to verify the
compiled constructor implements that menu. -/
theorem compilationFutureCorrect_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hGuarded : body.GuardedOccurrences name False)
    (hBodyFuture : RecursionBodyFutureCorrect signature name body) :
    CompilationFutureCorrect signature (.recur name body) := by
  intro state residual hRelated
  cases hRelated with
  | recur_source =>
      let bodyFragment := compileTypeFuel signature
        (typeCompilationFuel body) body
      let recursion := buildRecursionAutomaton signature name bodyFragment
      let pending : PendingAutomaton :=
        { states := recursion.states, edges := recursion.edges }
      have hFuel := typeCompilationFuel_sufficient body
      have hInitial : bodyFragment.initial ∈ bodyFragment.states :=
        compileTypeFuel_initial_mem signature (typeCompilationFuel body) body
          hFuel
      have hTargets : bodyFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature
          (typeCompilationFuel body) body hFuel
      have hRoot : computeFuture pending .root =
          computeFuture pending (.child 0 bodyFragment.initial) := by
        simpa [pending, recursion] using
          buildRecursionAutomaton_computeFuture_root signature name
            bodyFragment hTargets hInitial
      have hInitialRelation : TypeCompilationRelation body
          bodyFragment.initial body :=
        compileTypeFuel_initial_relation signature
          (typeCompilationFuel body) body hFuel
      have hEntry : computeFuture pending (.child 0 bodyFragment.initial) =
          typeFutureOffers (body.replaceVar name (.recur name body)) := by
        simpa [RecursionBodyFutureCorrect, bodyFragment, recursion, pending]
          using hBodyFuture bodyFragment.initial body hInitialRelation
      have hUnfold := guardedOccurrences_replace_typeFutureOffers_recur
        name body body hGuarded
      have hSyntax := typeFutureOffers_recur name body
      have hResult : computeFuture pending .root =
          typeFutureOffers (.recur name body) :=
        hRoot.trans (hEntry.trans (hUnfold.trans hSyntax.symm))
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        bodyFragment, recursion, pending] using hResult
  | recur_body _ _ childResidual childState hChildRelated =>
      have hBody := hBodyFuture childState childResidual hChildRelated
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hBody

/-- The recursion-specific tagged-body obligation.  It interprets matching
variable markers as calls of the surrounding binder and resolves symbolic
futures after the binder installs its backedges. -/
def RecursionBodyStepCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.recur name body)) (.recur name body)
  ∀ {state : TypeAutomatonState} {residual residual' : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation body state residual →
    env ∈ signature.localEnvironments →
    (DecoratedTypeTransition env
        (residual.replaceVar name (.recur name body)) label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge (.child 0 state) env label offers target ∧
        TypeCompilationRelation (.recur name body) target residual')

/-- Inversion of a decorated recursion-header transition. -/
private theorem TypeTransition.recur_fields
    {env : TypeEnvironment} {name : String} {body target : PactType}
    {label : TypeLabel}
    (hTransition : TypeTransition env (.recur name body) label target) :
    env.WellFormed ∧ label = TypeLabel.silent ∧
      target = body.replaceVar name (.recur name body) := by
  cases hTransition <;> simp_all

private theorem TypeOffers.recur_fields
    {env : TypeEnvironment} {name : String} {body target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.recur name body) label target current future) :
    label = TypeLabel.silent ∧
      target = body.replaceVar name (.recur name body) ∧
      current = ∅ ∧
      future = typeFutureOffers
        (body.replaceVar name (.recur name body)) := by
  cases hOffers <;> simp_all

theorem decoratedTypeTransition_recur_iff
    (env : TypeEnvironment) (name : String) (body target : PactType)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    DecoratedTypeTransition env (.recur name body) label offers target ↔
      env.WellFormed ∧ label = TypeLabel.silent ∧
        target = body.replaceVar name (.recur name body) ∧
        offers.current = ∅ ∧
        offers.future =
          typeFutureOffers (body.replaceVar name (.recur name body)) := by
  constructor
  · rintro ⟨hTransition, hOffers⟩
    have hTransitionFields := TypeTransition.recur_fields hTransition
    have hOfferFields := TypeOffers.recur_fields hOffers
    exact ⟨hTransitionFields.1, hTransitionFields.2.1,
      hTransitionFields.2.2, hOfferFields.2.2.1,
      hOfferFields.2.2.2⟩
  · rintro ⟨hWellFormed, rfl, rfl, hCurrent, hFuture⟩
    cases offers
    simp only at hCurrent hFuture
    subst_vars
    exact ⟨TypeTransition.recur env name body hWellFormed,
      TypeOffers.recur env name body hWellFormed⟩

/-- The root-state branch of raw recursion correspondence.  Guardedness and
tail-recursiveness enter later, when the two body invariants are established. -/
theorem compilationFragmentStepCorrect_recursion_root
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    {residual' : PactType} {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hLocalEnvironment : env ∈ signature.localEnvironments) :
    DecoratedTypeTransition env (.recur name body) label offers residual' ↔
      ∃ state',
        (compileTypeFuel signature
          (typeCompilationFuel (.recur name body))
          (.recur name body)).HasResolvedEdge .root env label offers state' ∧
        TypeCompilationRelation (.recur name body) state' residual' := by
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let recursion := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := recursion.states, edges := recursion.edges }
  have hBodyInitial : TypeCompilationRelation body bodyFragment.initial body := by
    exact compileTypeFuel_initial_relation signature
      (typeCompilationFuel body) body
      (typeCompilationFuel_sufficient body)
  have hComputed : computeFuture pending (.child 0 bodyFragment.initial) =
      typeFutureOffers (body.replaceVar name (.recur name body)) := by
    have hAmbient := hFuture bodyFragment.initial body hBodyInitial
    simpa [RecursionBodyFutureCorrect, bodyFragment, recursion, pending]
      using hAmbient
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.recur name body)) (.recur name body) =
        recursion := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hTargetRelation : TypeCompilationRelation (.recur name body)
      (.child 0 bodyFragment.initial)
      (body.replaceVar name (.recur name body)) :=
    TypeCompilationRelation.recur_body name body body _ hBodyInitial
  constructor
  · intro hStep
    rcases (decoratedTypeTransition_recur_iff env name body residual'
      label offers).mp hStep with
      ⟨hWellFormed, hLabel, hResidual, hCurrent, hOfferFuture⟩
    subst residual'
    refine ⟨.child 0 bodyFragment.initial, ?_, hTargetRelation⟩
    rw [hFragment]
    apply (buildRecursionAutomaton_root_hasResolvedEdge_iff signature name
      bodyFragment env label offers (.child 0 bodyFragment.initial)).mpr
    exact ⟨hLocalEnvironment, hLabel, hCurrent, hComputed.trans
      hOfferFuture.symm, rfl⟩
  · rintro ⟨target, hEdge, hTarget⟩
    rw [hFragment] at hEdge
    rcases (buildRecursionAutomaton_root_hasResolvedEdge_iff signature name
      bodyFragment env label offers target).mp hEdge with
      ⟨_, hLabel, hCurrent, hEdgeFuture, hTargetState⟩
    subst target
    have hResidual : residual' =
        body.replaceVar name (.recur name body) :=
      TypeCompilationRelation.residual_unique hTarget hTargetRelation
    apply (decoratedTypeTransition_recur_iff env name body residual'
      label offers).mpr
    exact ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
      hLabel, hResidual, hCurrent,
      (hComputed.symm.trans hEdgeFuture).symm⟩

/-- The header and tagged-body branches compose into raw recursion step
correspondence once their two closed-graph invariants are available. -/
theorem compilationFragmentStepCorrect_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyStepCorrect signature name body) :
    CompilationFragmentStepCorrect signature (.recur name body) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  cases hRelated with
  | recur_source =>
      exact compilationFragmentStepCorrect_recursion_root signature name body
        hFuture hLocalEnvironment
  | recur_body _ _ childResidual childState hChildRelated =>
      exact hBodyStep hChildRelated hLocalEnvironment

/-- Raw fragment correspondence exports uniformly through the fixed public
alphabet filter. -/
theorem compilationStepCorrect_of_fragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType)
    (hRaw : CompilationFragmentStepCorrect signature processType) :
    CompilationStepCorrect signature processType := by
  intro residual residual' state env label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLocalEnvironment : env ∈ signature.localEnvironments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact signature.environments_subset_localEnvironments hFields.1
  have hFragment := hRaw (residual' := residual') (label := label)
    (offers := offers) hRelated hLocalEnvironment
  constructor
  · intro hStep
    rcases hFragment.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType
        state target env label offers hSignatureSymbol).mpr hEdge,
      hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hFragment.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType
        state target env label offers hSignatureSymbol).mp hEdge,
      hTarget⟩

/-- Public recursion correspondence follows from the two closed-graph
recursion invariants. -/
theorem compilationStepCorrect_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyStepCorrect signature name body) :
    CompilationStepCorrect signature (.recur name body) :=
  compilationStepCorrect_of_fragmentStepCorrect signature (.recur name body)
    (compilationFragmentStepCorrect_recursion signature name body
      hFuture hBodyStep)

/-- Every compiled parallel edge hides immediate interface actions. -/
theorem compileType_parallel_edge_hides_immediate_interface
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType signature (.par left right interface)).HasEdge
      source env label offers target) :
    ∀ action ∈ env.immediate, action.1 ∉ interface := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | future => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        have hEnvironment := congrArg
          (fun edge : TypeAutomatonEdge => edge.symbol.environment) hOutput
        simp only at hEnvironment
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        change env = pendingEdge.environment at hEnvironment
        have hFuel :
            typeCompilationFuel (.par left right interface) =
              Nat.succ (max (typeCompilationFuel left)
                (typeCompilationFuel right)) := by
          rw [typeCompilationFuel]
          omega
        rw [hFuel] at hPendingEdge
        simp only [compileTypeFuel] at hPendingEdge
        change pendingEdge ∈
            (buildParallelAutomaton interface
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)).edges
          at hPendingEdge
        simp only [buildParallelAutomaton, finishAutomatonFragment]
          at hPendingEdge
        have hProductEdge := hPendingEdge
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter] at hProductEdge
        rcases hProductEdge with hTransition | hFuture
        · rcases hTransition with
            ⟨leftEdge, _, rightEdge, ⟨_, _⟩, rfl⟩
          intro action hAction hInterface
          rw [hEnvironment] at hAction
          unfold combineAutomatonEnvironment at hAction
          split at hAction
          · simp [TypeEnvironment.tock] at hAction
          · exact (Finset.mem_filter.mp hAction).2 hInterface
        · rcases hFuture with hLeftFuture | hRightFuture
          · rcases hLeftFuture with
              ⟨leftState, _, rightState, _, hEdge⟩
            rw [← hEdge] at hLabel
            simp at hLabel
          · rcases hRightFuture with
              ⟨leftState, _, rightState, _, hEdge⟩
            rw [← hEdge] at hLabel
            simp at hLabel
      · simp at hOutput

end

end Pact
