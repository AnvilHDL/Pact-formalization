import Anvilpp.PactTypes.Correspondence.CorrespondenceVisibility

/-!
# Parallel-product correspondence

Resolved product-edge classifiers and synchronization reconstruction.  These
lemmas concern step structure only and do not define operational futures.
-/

namespace Pact

noncomputable section

/-! ### Parallel-product correspondence -/

/-- A visible resolved child edge is exactly the record form of the raw
`HasResolvedEdge` relation. -/
private theorem mem_resolvedAutomatonEdges_visible_iff
    (fragment : AutomatonFragment) (source target : TypeAutomatonState)
    (environment : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) :
    ({ source := source
       environment := environment
       label := .visible label
       current := offers.current
       future := offers.future
       target := target } : AutomatonFragmentEdge) ∈
        resolvedAutomatonEdges fragment ↔
      fragment.HasResolvedEdge source environment label offers target := by
  classical
  simp only [resolvedAutomatonEdges, Finset.mem_image,
    AutomatonFragment.HasResolvedEdge]
  constructor
  · rintro ⟨edge, hEdge, hResolved⟩
    have hSource := congrArg AutomatonFragmentEdge.source hResolved
    have hEnvironment := congrArg AutomatonFragmentEdge.environment hResolved
    have hLabel := congrArg AutomatonFragmentEdge.label hResolved
    have hCurrent := congrArg AutomatonFragmentEdge.current hResolved
    have hFuture := congrArg AutomatonFragmentEdge.future hResolved
    have hTarget := congrArg AutomatonFragmentEdge.target hResolved
    refine ⟨edge, hEdge, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hSource
    · simpa using hEnvironment
    · simpa using hLabel
    · simpa using hCurrent
    · simpa using hFuture
    · simpa using hTarget
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    refine ⟨edge, hEdge, ?_⟩
    cases edge
    simp_all
    exact hFuture

/-- Offer derivations carry the matching undecorated transition.  This is used
for the independent sibling-offer witnesses in the parallel product. -/
theorem TypeOffers.to_transition
    {environment : TypeEnvironment} {source target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers environment source label target current future) :
    TypeTransition environment source label target := by
  apply TypeOffers.rec
    (motive_1 := fun env source label target _ _ _ =>
      TypeTransition env source label target)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
  all_goals aesop
  exact TypeTransition.xoffer_branch env elseType branches (fst, snd)
    processType ⟨left, left_1, left_2, right⟩

private theorem restrictTypeOffers_subset_localEnvironmentActions
    (signature : TypeAlphabet) (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (offers : Finset BareMessage) :
    restrictTypeOffers interface offers ⊆
      signature.localEnvironmentActions := by
  intro action hAction
  rcases action with ⟨message, direction⟩
  have hInternal : message ∈ signature.interface :=
    hInterface (Finset.mem_filter.mp hAction).2
  simp only [TypeAlphabet.localEnvironmentActions, Finset.mem_image]
  cases direction
  · refine ⟨(message, MessageDir.recv), ?_, rfl⟩
    simp [TypeAlphabet.localActions, TypeAlphabet.interfaceActions, hInternal]
  · refine ⟨(message, MessageDir.send), ?_, rfl⟩
    simp [TypeAlphabet.localActions, TypeAlphabet.interfaceActions, hInternal]

/-- A semantic sibling-local environment stays inside the compiler's local
universe when its outer environment is already construction-local. -/
private theorem TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment_local
    (signature : TypeAlphabet) (interface : Interface)
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {sibling : PactType} {label : TypeLabel}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.localEnvironments)
    (hLocal : LocalTypeEnvironment outer interface siblingEnvironment sibling
      label localEnvironment) :
    localEnvironment ∈ signature.localEnvironments := by
  cases hLocal with
  | clock outer interface sibling label hClock =>
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | ordinary outer siblingEnvironment localEnvironment interface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image] at hOuter
      rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
        outerFuture, hOuterFuture, hOuter⟩
      · subst outer
        simp [TypeEnvironment.tock] at hOuterClock
      · subst outer
        simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
          Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
          Finset.mem_image]
        right
        refine ⟨localEnvironment.immediate, ?_, localEnvironment.future, ?_, ?_⟩
        · rw [hImmediate]
          apply Finset.union_subset
          · exact hOuterImmediate
          · exact restrictTypeOffers_subset_localEnvironmentActions signature
              interface hInterface current
        · rw [hFuture]
          intro action hAction
          have hAvailable := Finset.mem_sdiff.mp hAction
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, hAvailable.2⟩
          rcases Finset.mem_union.mp hAvailable.1 with hBoundary | hInternal
          · exact (Finset.mem_sdiff.mp (hOuterFuture hBoundary)).1
          · exact restrictTypeOffers_subset_localEnvironmentActions signature
              interface hInterface future hInternal
        · cases localEnvironment
          simp_all

/-- A semantic sibling-local environment is contained in the compiler's local
environment universe whenever its outer environment is exported and the
constructor interface is declared by the signature. -/
private theorem TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment
    (signature : TypeAlphabet) (interface : Interface)
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {sibling : PactType} {label : TypeLabel}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.environments)
    (hLocal : LocalTypeEnvironment outer interface siblingEnvironment sibling
      label localEnvironment) :
    localEnvironment ∈ signature.localEnvironments := by
  cases hLocal with
  | clock outer interface sibling label hClock =>
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | ordinary outer siblingEnvironment localEnvironment interface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      simp only [TypeAlphabet.environments, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image] at hOuter
      rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
        outerFuture, hOuterFuture, hOuter⟩
      · subst outer
        simp [TypeEnvironment.tock] at hOuterClock
      · subst outer
        simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
          Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
          Finset.mem_image]
        right
        refine ⟨localEnvironment.immediate, ?_, localEnvironment.future, ?_, ?_⟩
        · rw [hImmediate]
          apply Finset.union_subset
          · exact hOuterImmediate.trans
              (signature.environmentActions_subset_localEnvironmentActions)
          · exact restrictTypeOffers_subset_localEnvironmentActions signature
              interface hInterface current
        · rw [hFuture]
          intro action hAction
          have hAvailable := Finset.mem_sdiff.mp hAction
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, hAvailable.2⟩
          rcases Finset.mem_union.mp hAvailable.1 with hBoundary | hInternal
          · exact signature.environmentActions_subset_localEnvironmentActions
              (Finset.mem_sdiff.mp (hOuterFuture hBoundary)).1
          · exact restrictTypeOffers_subset_localEnvironmentActions signature
              interface hInterface future hInternal
        · cases localEnvironment
          simp_all

/-- The set-theoretic fields of an ordinary sibling-local environment are
enough to place it in the compiler's local environment universe.  This
version does not require the semantic offer derivation and is therefore
usable before synchronization witnesses have been reconstructed. -/
private theorem TypeAlphabet.localEnvironment_mem_of_ordinary_fields
    (signature : TypeAlphabet) (interface : Interface)
    {outer localEnvironment : TypeEnvironment}
    {current future : Finset BareMessage}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.environments)
    (hOuterClock : outer.clock = false)
    (hLocalClock : localEnvironment.clock = false)
    (hImmediate : localEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface current)
    (hFuture : localEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface future) \
        localEnvironment.immediate) :
    localEnvironment ∈ signature.localEnvironments := by
  simp only [TypeAlphabet.environments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image] at hOuter
  rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
    outerFuture, hOuterFuture, hOuter⟩
  · subst outer
    simp [TypeEnvironment.tock] at hOuterClock
  · subst outer
    simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
      Finset.mem_image]
    right
    refine ⟨localEnvironment.immediate, ?_, localEnvironment.future, ?_, ?_⟩
    · rw [hImmediate]
      apply Finset.union_subset
      · exact hOuterImmediate.trans
          signature.environmentActions_subset_localEnvironmentActions
      · exact restrictTypeOffers_subset_localEnvironmentActions signature
          interface hInterface current
    · rw [hFuture]
      intro action hAction
      have hAvailable := Finset.mem_sdiff.mp hAction
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hAvailable.2⟩
      rcases Finset.mem_union.mp hAvailable.1 with hBoundary | hInternal
      · exact signature.environmentActions_subset_localEnvironmentActions
          (Finset.mem_sdiff.mp (hOuterFuture hBoundary)).1
      · exact restrictTypeOffers_subset_localEnvironmentActions signature
          interface hInterface future hInternal
    · cases localEnvironment
      simp_all

/-- Ordinary local-environment fields preserve the construction-local
environment universe when the outer environment is itself construction-local. -/
private theorem TypeAlphabet.localEnvironment_mem_of_ordinary_fields_local
    (signature : TypeAlphabet) (interface : Interface)
    {outer localEnvironment : TypeEnvironment}
    {current future : Finset BareMessage}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.localEnvironments)
    (hOuterClock : outer.clock = false)
    (hLocalClock : localEnvironment.clock = false)
    (hImmediate : localEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface current)
    (hFuture : localEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface future) \
        localEnvironment.immediate) :
    localEnvironment ∈ signature.localEnvironments := by
  simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image] at hOuter
  rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
    outerFuture, hOuterFuture, hOuter⟩
  · subst outer
    simp [TypeEnvironment.tock] at hOuterClock
  · subst outer
    simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
      Finset.mem_image]
    right
    refine ⟨localEnvironment.immediate, ?_, localEnvironment.future, ?_, ?_⟩
    · rw [hImmediate]
      apply Finset.union_subset
      · exact hOuterImmediate
      · exact restrictTypeOffers_subset_localEnvironmentActions signature
          interface hInterface current
    · rw [hFuture]
      intro action hAction
      have hAvailable := Finset.mem_sdiff.mp hAction
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hAvailable.2⟩
      rcases Finset.mem_union.mp hAvailable.1 with hBoundary | hInternal
      · exact (Finset.mem_sdiff.mp (hOuterFuture hBoundary)).1
      · exact restrictTypeOffers_subset_localEnvironmentActions signature
          interface hInterface future hInternal
    · cases localEnvironment
      simp_all

/-- A synchronized product witness over an exported outer environment forces
both component environments into the compiler's local environment domain. -/
private theorem TypeAlphabet.localEnvironments_of_syncAutomatonEdgeWitnesses
    (signature : TypeAlphabet) (interface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    left.environment ∈ signature.localEnvironments ∧
      right.environment ∈ signature.localEnvironments := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨_, _, hFields, _⟩
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨hLeftClock', hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      have hCombinedEnvironment :
          combineAutomatonEnvironment interface left.environment
              right.environment ∈ signature.environments := by
        rw [hOuter]
        exact hOuterEnvironment
      have hCombinedClock :
          (combineAutomatonEnvironment interface left.environment
              right.environment).clock = false := by
        simp [combineAutomatonEnvironment, hLeftClock]
      exact ⟨
        TypeAlphabet.localEnvironment_mem_of_ordinary_fields signature
          interface hInterface hCombinedEnvironment hCombinedClock
          hLeftClock hLeftImmediate hLeftFuture,
        TypeAlphabet.localEnvironment_mem_of_ordinary_fields signature
          interface hInterface hCombinedEnvironment hCombinedClock
          hRightClock hRightImmediate hRightFuture⟩

/-- Local-domain counterpart of
`localEnvironments_of_syncAutomatonEdgeWitnesses`. -/
private theorem TypeAlphabet.localEnvironments_of_syncAutomatonEdgeWitnesses_local
    (signature : TypeAlphabet) (interface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.localEnvironments)
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    left.environment ∈ signature.localEnvironments ∧
      right.environment ∈ signature.localEnvironments := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨_, _, hFields, _⟩
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨_, hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      have hCombinedEnvironment :
          combineAutomatonEnvironment interface left.environment
              right.environment ∈ signature.localEnvironments := by
        rw [hOuter]
        exact hOuterEnvironment
      have hCombinedClock :
          (combineAutomatonEnvironment interface left.environment
              right.environment).clock = false := by
        simp [combineAutomatonEnvironment, hLeftClock]
      exact ⟨
        TypeAlphabet.localEnvironment_mem_of_ordinary_fields_local signature
          interface hInterface hCombinedEnvironment hCombinedClock
          hLeftClock hLeftImmediate hLeftFuture,
        TypeAlphabet.localEnvironment_mem_of_ordinary_fields_local signature
          interface hInterface hCombinedEnvironment hCombinedClock
          hRightClock hRightImmediate hRightFuture⟩

/-- Synchronization field equations preserve avoidance of every descendant
interface disjoint from the product's own interface. -/
private theorem syncAutomatonEdgeWitnesses_environments_avoid
    (interface childInterface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hOuterAvoids : outer.AvoidsInterface childInterface)
    (hDisjoint : Disjoint interface childInterface)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    left.environment.AvoidsInterface childInterface ∧
      right.environment.AvoidsInterface childInterface := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨_, _, hFields, _⟩
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      exact ⟨TypeEnvironment.tock_avoidsInterface childInterface,
        TypeEnvironment.tock_avoidsInterface childInterface⟩
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨hLeftClock', hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      have hCombinedAvoids :
          (combineAutomatonEnvironment interface left.environment
              right.environment).AvoidsInterface childInterface := by
        rw [hOuter]
        exact hOuterAvoids
      exact ⟨
        TypeEnvironment.avoidsInterface_of_ordinary_fields hCombinedAvoids
          hDisjoint hLeftImmediate hLeftFuture,
        TypeEnvironment.avoidsInterface_of_ordinary_fields hCombinedAvoids
          hDisjoint hRightImmediate hRightFuture⟩

private def semanticResolvedAutomatonEdges
    (fragment : AutomatonFragment) : Finset AutomatonFragmentEdge :=
  (resolvedAutomatonEdges fragment).filter fun edge =>
    edge.label ≠ .future

private theorem AutomatonConstructionLabel.combine_eq_visible_iff
    (interface : Interface) (left right : AutomatonConstructionLabel)
    (label : TypeLabel) :
    AutomatonConstructionLabel.combine interface left right = .visible label ↔
      ∃ leftLabel rightLabel,
        left = .visible leftLabel ∧ right = .visible rightLabel ∧
          TypeLabel.combine interface leftLabel rightLabel = label := by
  cases left <;> cases right <;>
    simp [AutomatonConstructionLabel.combine]

/- Exact visible resolved-edge classifier for the synchronized product.
Construction-only optimistic-future observations are excluded here. -/
private theorem buildParallelAutomaton_hasResolvedEdge_iff
    (interface : Interface) (left right : AutomatonFragment)
    (leftSource rightSource leftTarget rightTarget : TypeAutomatonState)
    (environment : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) :
    (buildParallelAutomaton interface left right).HasResolvedEdge
        (.pair leftSource rightSource) environment label offers
        (.pair leftTarget rightTarget) ↔
      ∃ leftEdge ∈ semanticResolvedAutomatonEdges left,
        ∃ rightEdge ∈ semanticResolvedAutomatonEdges right,
          leftEdge.source = leftSource ∧ rightEdge.source = rightSource ∧
          syncAutomatonEdges interface (semanticResolvedAutomatonEdges left)
              (semanticResolvedAutomatonEdges right) leftEdge rightEdge ∧
          combineAutomatonEnvironment interface leftEdge.environment
              rightEdge.environment = environment ∧
          AutomatonConstructionLabel.combine interface leftEdge.label
              rightEdge.label = .visible label ∧
          hideOffers interface (leftEdge.current ∪ rightEdge.current) =
              offers.current ∧
          hideOffers interface (leftEdge.future ∪ rightEdge.future) =
              offers.future ∧
          leftEdge.target = leftTarget ∧ rightEdge.target = rightTarget := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with
        ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, hSync⟩, rfl⟩
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      injection hSource with hLeftSource hRightSource
      injection hTarget with hLeftTarget hRightTarget
      exact ⟨leftEdge,
        (by simpa [semanticResolvedAutomatonEdges] using hLeftEdge),
        rightEdge,
        (by simpa [semanticResolvedAutomatonEdges] using hRightEdge),
        hLeftSource, hRightSource,
        (by simpa [semanticResolvedAutomatonEdges] using hSync),
        hEnvironment, hLabel, hCurrent, hFuture, hLeftTarget, hRightTarget⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftState, _, rightState, _, rfl⟩
        simp at hLabel
      · rcases hRight with ⟨leftState, _, rightState, _, rfl⟩
        simp at hLabel
  · rintro ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge,
      hLeftSource, hRightSource, hSync, hEnvironment, hLabel, hCurrent,
      hFuture, hLeftTarget, hRightTarget⟩
    let edge : PendingAutomatonEdge :=
      { source := .pair leftEdge.source rightEdge.source
        environment := combineAutomatonEnvironment interface
          leftEdge.environment rightEdge.environment
        label := AutomatonConstructionLabel.combine interface leftEdge.label
          rightEdge.label
        current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
        future := .explicit
          (hideOffers interface (leftEdge.future ∪ rightEdge.future))
        target := .pair leftEdge.target rightEdge.target }
    refine ⟨edge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_filter]
      left
      have hLeftRaw := hLeftEdge
      have hRightRaw := hRightEdge
      simp only [semanticResolvedAutomatonEdges, Finset.mem_filter]
        at hLeftRaw hRightRaw
      exact ⟨leftEdge, hLeftRaw, rightEdge, ⟨hRightRaw, hSync⟩, rfl⟩
    · simp [edge, hLeftSource, hRightSource]
    · simpa [edge] using hEnvironment
    · simpa [edge] using hLabel
    · simpa [edge] using hCurrent
    · simpa [edge] using hFuture
    · simp [edge, hLeftTarget, hRightTarget]
/-- Canonical compiler-fragment form of the synchronized product classifier. -/
theorem compileTypeFuel_parallel_hasResolvedEdge_iff
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (leftSource rightSource leftTarget rightTarget : TypeAutomatonState)
    (environment : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature
          (typeCompilationFuel (.par left right interface))
          (.par left right interface))
        (.pair leftSource rightSource) environment label offers
        (.pair leftTarget rightTarget) ↔
      ∃ leftEnvironment rightEnvironment leftLabel rightLabel
          leftOffers rightOffers,
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
            leftSource leftEnvironment leftLabel leftOffers leftTarget ∧
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel right) right)
            rightSource rightEnvironment rightLabel rightOffers rightTarget ∧
        let leftEdge : AutomatonFragmentEdge :=
          { source := leftSource
            environment := leftEnvironment
            label := .visible leftLabel
            current := leftOffers.current
            future := leftOffers.future
            target := leftTarget }
        let rightEdge : AutomatonFragmentEdge :=
          { source := rightSource
            environment := rightEnvironment
            label := .visible rightLabel
            current := rightOffers.current
            future := rightOffers.future
            target := rightTarget }
        syncAutomatonEdges interface
            (semanticResolvedAutomatonEdges (compileTypeFuel signature
              (typeCompilationFuel left) left))
            (semanticResolvedAutomatonEdges (compileTypeFuel signature
              (typeCompilationFuel right) right)) leftEdge rightEdge ∧
          combineAutomatonEnvironment interface leftEnvironment
              rightEnvironment = environment ∧
          TypeLabel.combine interface leftLabel rightLabel = label ∧
          hideOffers interface (leftOffers.current ∪ rightOffers.current) =
              offers.current ∧
          hideOffers interface (leftOffers.future ∪ rightOffers.future) =
              offers.future := by
  classical
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.par left right interface))
          (.par left right interface) =
        buildParallelAutomaton interface leftFragment rightFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  constructor
  · intro hEdge
    rcases (buildParallelAutomaton_hasResolvedEdge_iff interface leftFragment
      rightFragment leftSource rightSource leftTarget rightTarget environment
      label offers).mp hEdge with
      ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, hLeftSource, hRightSource,
        hSync, hEnvironment, hLabel, hCurrent, hFuture, hLeftTarget,
        hRightTarget⟩
    rcases (AutomatonConstructionLabel.combine_eq_visible_iff interface
      leftEdge.label rightEdge.label label).mp hLabel with
      ⟨leftLabel, rightLabel, hLeftLabel, hRightLabel, hLabel⟩
    let leftOffers : TypeOfferSummary :=
      { current := leftEdge.current, future := leftEdge.future }
    let rightOffers : TypeOfferSummary :=
      { current := rightEdge.current, future := rightEdge.future }
    let leftShape : AutomatonFragmentEdge :=
      { source := leftSource
        environment := leftEdge.environment
        label := .visible leftLabel
        current := leftEdge.current
        future := leftEdge.future
        target := leftTarget }
    let rightShape : AutomatonFragmentEdge :=
      { source := rightSource
        environment := rightEdge.environment
        label := .visible rightLabel
        current := rightEdge.current
        future := rightEdge.future
        target := rightTarget }
    have hLeftShape : leftShape = leftEdge := by
      cases leftEdge
      simp_all [leftShape]
    have hRightShape : rightShape = rightEdge := by
      cases rightEdge
      simp_all [rightShape]
    have hLeftResolved : AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel left) left)
        leftSource leftEdge.environment leftLabel leftOffers
        leftTarget := by
      have hLeftRaw := hLeftEdge
      simp only [semanticResolvedAutomatonEdges, Finset.mem_filter] at hLeftRaw
      rw [hLeftStable] at hLeftRaw
      apply (mem_resolvedAutomatonEdges_visible_iff
        (compileTypeFuel signature (typeCompilationFuel left) left)
        leftSource leftTarget leftEdge.environment leftLabel leftOffers).mp
      change leftShape ∈ resolvedAutomatonEdges
        (compileTypeFuel signature (typeCompilationFuel left) left)
      rw [hLeftShape]
      exact hLeftRaw.1
    have hRightResolved : AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel right) right)
        rightSource rightEdge.environment rightLabel rightOffers
        rightTarget := by
      have hRightRaw := hRightEdge
      simp only [semanticResolvedAutomatonEdges, Finset.mem_filter] at hRightRaw
      rw [hRightStable] at hRightRaw
      apply (mem_resolvedAutomatonEdges_visible_iff
        (compileTypeFuel signature (typeCompilationFuel right) right)
        rightSource rightTarget rightEdge.environment rightLabel rightOffers).mp
      change rightShape ∈ resolvedAutomatonEdges
        (compileTypeFuel signature (typeCompilationFuel right) right)
      rw [hRightShape]
      exact hRightRaw.1
    refine ⟨leftEdge.environment, rightEdge.environment, leftLabel,
      rightLabel, leftOffers, rightOffers, hLeftResolved, hRightResolved, ?_⟩
    dsimp only
    have hSync' := hSync
    rw [hLeftStable, hRightStable] at hSync'
    refine ⟨?_, hEnvironment, hLabel, ?_, ?_⟩
    · change syncAutomatonEdges interface _ _ leftShape rightShape
      simpa [hLeftShape, hRightShape] using hSync'
    · simpa [leftOffers, rightOffers] using hCurrent
    · simpa [leftOffers, rightOffers] using hFuture
  · rintro ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
      leftOffers, rightOffers, hLeftResolved, hRightResolved, hFields⟩
    dsimp only at hFields
    rcases hFields with ⟨hSync, hEnvironment, hLabel, hCurrent, hFuture⟩
    let leftEdge : AutomatonFragmentEdge :=
      { source := leftSource
        environment := leftEnvironment
        label := .visible leftLabel
        current := leftOffers.current
        future := leftOffers.future
        target := leftTarget }
    let rightEdge : AutomatonFragmentEdge :=
      { source := rightSource
        environment := rightEnvironment
        label := .visible rightLabel
        current := rightOffers.current
        future := rightOffers.future
        target := rightTarget }
    have hLeftEdge : leftEdge ∈ semanticResolvedAutomatonEdges leftFragment := by
      rw [hLeftStable]
      simp only [semanticResolvedAutomatonEdges, Finset.mem_filter]
      exact ⟨(mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
        hLeftResolved, by simp [leftEdge]⟩
    have hRightEdge : rightEdge ∈ semanticResolvedAutomatonEdges rightFragment := by
      rw [hRightStable]
      simp only [semanticResolvedAutomatonEdges, Finset.mem_filter]
      exact ⟨(mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
        hRightResolved, by simp [rightEdge]⟩
    apply (buildParallelAutomaton_hasResolvedEdge_iff interface leftFragment
      rightFragment leftSource rightSource leftTarget rightTarget environment
      label offers).mpr
    refine ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, rfl, rfl, ?_,
      hEnvironment, ?_, hCurrent, hFuture, rfl, rfl⟩
    · simpa [leftEdge, rightEdge, hLeftStable, hRightStable] using hSync
    · simpa [leftEdge, rightEdge,
        AutomatonConstructionLabel.combine] using hLabel


private theorem TypeOffers.parallel_fields
    {outer : TypeEnvironment} {left right target : PactType}
    {interface : Interface} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers outer (.par left right interface) label target
      current future) :
    ∃ leftEnvironment rightEnvironment leftTarget rightTarget
        leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture,
      target = .par leftTarget rightTarget interface ∧
      label = TypeLabel.combine interface leftLabel rightLabel ∧
      hideTypeOffers interface (leftCurrent ∪ rightCurrent) = current ∧
      hideTypeOffers interface (leftFuture ∪ rightFuture) = future ∧
      TypeOffers leftEnvironment left leftLabel leftTarget leftCurrent
        leftFuture ∧
      TypeOffers rightEnvironment right rightLabel rightTarget rightCurrent
        rightFuture ∧
      LocalTypeEnvironment outer interface rightEnvironment right rightLabel
        leftEnvironment ∧
      LocalTypeEnvironment outer interface leftEnvironment left leftLabel
        rightEnvironment ∧
      outer.WellFormed ∧ TypeLabel.Sync interface leftLabel rightLabel := by
  cases hOffers with
  | par outer leftEnvironment rightEnvironment interface left leftTarget right
      rightTarget leftLabel rightLabel leftCurrent leftFuture rightCurrent
      rightFuture hLeftOffers hRightOffers hLeftLocal hRightLocal hFields =>
      exact ⟨leftEnvironment, rightEnvironment, leftTarget, rightTarget,
        leftLabel, rightLabel, leftCurrent, leftFuture, rightCurrent,
        rightFuture, rfl, rfl, rfl, rfl, hLeftOffers, hRightOffers,
        hLeftLocal, hRightLocal, hFields⟩

/-- The forward half of scoped parallel correspondence.  A semantic product
step is compiled by reconstructing exactly the two synchronized visible child
edges selected by its local-environment premises. -/
theorem parallel_semantic_step_to_resolved_edge
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped (.par left right interface))
    (hLeftStep : CompilationScopedFragmentStepCorrect signature left)
    (hRightStep : CompilationScopedFragmentStepCorrect signature right)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.par left right interface) state
      residual)
    (hOuterEnvironment : environment ∈ signature.localEnvironments)
    (hOuterAvoids : environment.AvoidsInterface
      (PactType.ParallelInterfaces (PactType.par left right interface)))
    (hStep : DecoratedTypeTransition environment residual label offers
      residual') :
    ∃ target,
      (compileTypeFuel signature
        (typeCompilationFuel (.par left right interface))
        (.par left right interface)).HasResolvedEdge state environment label
          offers target ∧
      TypeCompilationRelation (.par left right interface) target residual' := by
  classical
  have hScopedFields := hScoped
  simp only [PactType.InterfaceScoped] at hScopedFields
  have hDisjointLeft : Disjoint interface left.ParallelInterfaces := by
    rw [Finset.disjoint_left] at hScopedFields ⊢
    intro message hInterfaceMessage hLeftMessage
    exact hScopedFields.1 hInterfaceMessage
      (Finset.mem_union_left _ hLeftMessage)
  have hDisjointRight : Disjoint interface right.ParallelInterfaces := by
    rw [Finset.disjoint_left] at hScopedFields ⊢
    intro message hInterfaceMessage hRightMessage
    exact hScopedFields.1 hInterfaceMessage
      (Finset.mem_union_right _ hRightMessage)
  have hInterfaceSubset : interface ⊆
      PactType.ParallelInterfaces (PactType.par left right interface) := by
    intro message hMessage
    simp only [PactType.ParallelInterfaces, Finset.mem_union]
    exact Or.inl (Or.inl hMessage)
  have hLeftSubset : left.ParallelInterfaces ⊆
      PactType.ParallelInterfaces (PactType.par left right interface) := by
    intro message hMessage
    simp only [PactType.ParallelInterfaces, Finset.mem_union]
    exact Or.inl (Or.inr hMessage)
  have hRightSubset : right.ParallelInterfaces ⊆
      PactType.ParallelInterfaces (PactType.par left right interface) := by
    intro message hMessage
    simp only [PactType.ParallelInterfaces, Finset.mem_union]
    exact Or.inr hMessage
  have hOuterAvoidsInterface := hOuterAvoids.mono hInterfaceSubset
  have hOuterAvoidsLeft := hOuterAvoids.mono hLeftSubset
  have hOuterAvoidsRight := hOuterAvoids.mono hRightSubset
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftState rightState
      hLeftRelated hRightRelated =>
      rcases hStep with ⟨_, hOffers⟩
      obtain ⟨leftEnvironment, rightEnvironment, leftTarget, rightTarget,
          leftLabel, rightLabel, leftCurrent, leftFuture, rightCurrent,
          rightFuture, hTarget, hLabel, hCurrent, hFuture, hLeftOffers,
          hRightOffers, hLeftLocal, hRightLocal, _, hLabelSync⟩ :=
        TypeOffers.parallel_fields hOffers
      have hLeftLocalEnvironment :
          leftEnvironment ∈ signature.localEnvironments :=
        TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment_local
          signature interface hInterface hOuterEnvironment hLeftLocal
      have hRightLocalEnvironment :
          rightEnvironment ∈ signature.localEnvironments :=
        TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment_local
          signature interface hInterface hOuterEnvironment hRightLocal
      have hLeftAvoids :
          leftEnvironment.AvoidsInterface left.ParallelInterfaces :=
        hLeftLocal.avoidsInterface_of_disjoint hOuterAvoidsLeft hDisjointLeft
      have hRightAvoids :
          rightEnvironment.AvoidsInterface right.ParallelInterfaces :=
        hRightLocal.avoidsInterface_of_disjoint hOuterAvoidsRight hDisjointRight
      rcases (hLeftStep (residual' := leftTarget) (label := leftLabel)
          (offers := { current := leftCurrent, future := leftFuture })
          hLeftRelated hLeftLocalEnvironment hLeftAvoids).mp
          ⟨TypeOffers.to_transition hLeftOffers, hLeftOffers⟩ with
        ⟨leftTargetState, hLeftEdge, hLeftTargetRelated⟩
      rcases (hRightStep (residual' := rightTarget) (label := rightLabel)
          (offers := { current := rightCurrent, future := rightFuture })
          hRightRelated hRightLocalEnvironment hRightAvoids).mp
          ⟨TypeOffers.to_transition hRightOffers, hRightOffers⟩ with
        ⟨rightTargetState, hRightEdge, hRightTargetRelated⟩
      let leftSummary : TypeOfferSummary :=
        { current := leftCurrent, future := leftFuture }
      let rightSummary : TypeOfferSummary :=
        { current := rightCurrent, future := rightFuture }
      let leftAutomatonEdge : AutomatonFragmentEdge :=
        { source := leftState
          environment := leftEnvironment
          label := .visible leftLabel
          current := leftCurrent
          future := leftFuture
          target := leftTargetState }
      let rightAutomatonEdge : AutomatonFragmentEdge :=
        { source := rightState
          environment := rightEnvironment
          label := .visible rightLabel
          current := rightCurrent
          future := rightFuture
          target := rightTargetState }
      have hLeftEdgeMember : leftAutomatonEdge ∈
          semanticResolvedAutomatonEdges (compileTypeFuel signature
            (typeCompilationFuel left) left) := by
        simp only [semanticResolvedAutomatonEdges, Finset.mem_filter]
        exact ⟨(mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
          hLeftEdge, by simp [leftAutomatonEdge]⟩
      have hRightEdgeMember : rightAutomatonEdge ∈
          semanticResolvedAutomatonEdges (compileTypeFuel signature
            (typeCompilationFuel right) right) := by
        simp only [semanticResolvedAutomatonEdges, Finset.mem_filter]
        exact ⟨(mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
          hRightEdge, by simp [rightAutomatonEdge]⟩
      have hLeftRealizes :
          ∀ {target current future},
            TypeOffers leftEnvironment leftResidual leftLabel target current
                future →
            ∃ witness ∈ semanticResolvedAutomatonEdges
                (compileTypeFuel signature (typeCompilationFuel left) left),
              matchesAutomatonOfferWitness leftAutomatonEdge witness ∧
                witness.current = current ∧ witness.future = future := by
        intro target current future hSiblingOffers
        rcases (hLeftStep (residual' := target) (label := leftLabel)
            (offers := { current := current, future := future })
            hLeftRelated hLeftLocalEnvironment hLeftAvoids).mp
            ⟨TypeOffers.to_transition hSiblingOffers, hSiblingOffers⟩ with
          ⟨targetState, hResolved, _⟩
        let witness : AutomatonFragmentEdge :=
          { source := leftState
            environment := leftEnvironment
            label := .visible leftLabel
            current := current
            future := future
            target := targetState }
        refine ⟨witness, ?_, ?_, rfl, rfl⟩
        · simp only [semanticResolvedAutomatonEdges, Finset.mem_filter]
          exact ⟨(mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
            hResolved, by simp [witness]⟩
        · simp [matchesAutomatonOfferWitness, leftAutomatonEdge, witness,
            AutomatonConstructionLabel.semantic]
      have hRightRealizes :
          ∀ {target current future},
            TypeOffers rightEnvironment rightResidual rightLabel target current
                future →
            ∃ witness ∈ semanticResolvedAutomatonEdges
                (compileTypeFuel signature (typeCompilationFuel right) right),
              matchesAutomatonOfferWitness rightAutomatonEdge witness ∧
                witness.current = current ∧ witness.future = future := by
        intro target current future hSiblingOffers
        rcases (hRightStep (residual' := target) (label := rightLabel)
            (offers := { current := current, future := future })
            hRightRelated hRightLocalEnvironment hRightAvoids).mp
            ⟨TypeOffers.to_transition hSiblingOffers, hSiblingOffers⟩ with
          ⟨targetState, hResolved, _⟩
        let witness : AutomatonFragmentEdge :=
          { source := rightState
            environment := rightEnvironment
            label := .visible rightLabel
            current := current
            future := future
            target := targetState }
        refine ⟨witness, ?_, ?_, rfl, rfl⟩
        · simp only [semanticResolvedAutomatonEdges, Finset.mem_filter]
          exact ⟨(mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
            hResolved, by simp [witness]⟩
        · simp [matchesAutomatonOfferWitness, rightAutomatonEdge, witness,
            AutomatonConstructionLabel.semantic]
      obtain ⟨hSynchronized, hCombinedEnvironment⟩ :=
        localTypeEnvironments_to_syncAutomatonEdges_local signature interface
          hInterface hOuterEnvironment hOuterAvoidsInterface hLeftEdgeMember
          hRightEdgeMember hLeftLocal hRightLocal hLeftRealizes hRightRealizes
          hLabelSync
      refine ⟨.pair leftTargetState rightTargetState, ?_, ?_⟩
      · apply (compileTypeFuel_parallel_hasResolvedEdge_iff signature left right
          interface leftState rightState leftTargetState rightTargetState
          environment label { current := current, future := future }).mpr
        refine ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
          leftSummary, rightSummary, hLeftEdge, hRightEdge, ?_⟩
        dsimp only
        refine ⟨?_, hCombinedEnvironment, hLabel.symm, ?_, ?_⟩
        · simpa [leftAutomatonEdge, rightAutomatonEdge, leftSummary,
            rightSummary] using hSynchronized
        · simpa [leftSummary, rightSummary, hideOffers, hideTypeOffers]
            using hCurrent
        · simpa [leftSummary, rightSummary, hideOffers, hideTypeOffers]
            using hFuture
      · rw [hTarget]
        exact TypeCompilationRelation.parallel left right leftTarget rightTarget
          interface leftTargetState rightTargetState hLeftTargetRelated
          hRightTargetRelated

/-- The reverse half of scoped parallel correspondence.  The product edge
stores actual child targets but may use independent same-source offer witnesses
to determine the two local environments; witness correctness reconstructs
exactly those semantic sibling judgments. -/
theorem parallel_resolved_edge_to_semantic_step
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped (.par left right interface))
    (hLeftStep : CompilationScopedFragmentStepCorrect signature left)
    (hRightStep : CompilationScopedFragmentStepCorrect signature right)
    (hLeftWitness :
      CompilationScopedResolvedOfferWitnessCorrect signature left)
    (hRightWitness :
      CompilationScopedResolvedOfferWitnessCorrect signature right)
    {residual residual' : PactType} {state target : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.par left right interface) state
      residual)
    (hOuterEnvironment : environment ∈ signature.localEnvironments)
    (hOuterAvoids : environment.AvoidsInterface
      (PactType.par left right interface).ParallelInterfaces)
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.par left right interface))
      (.par left right interface)).HasResolvedEdge state environment label
        offers target)
    (hTargetRelated : TypeCompilationRelation (.par left right interface)
      target residual') :
    DecoratedTypeTransition environment residual label offers residual' := by
  classical
  have hScopedFields := hScoped
  simp only [PactType.InterfaceScoped] at hScopedFields
  have hDisjointLeft : Disjoint interface left.ParallelInterfaces := by
    rw [Finset.disjoint_left] at hScopedFields ⊢
    intro message hInterfaceMessage hLeftMessage
    exact hScopedFields.1 hInterfaceMessage
      (Finset.mem_union_left _ hLeftMessage)
  have hDisjointRight : Disjoint interface right.ParallelInterfaces := by
    rw [Finset.disjoint_left] at hScopedFields ⊢
    intro message hInterfaceMessage hRightMessage
    exact hScopedFields.1 hInterfaceMessage
      (Finset.mem_union_right _ hRightMessage)
  have hLeftSubset : left.ParallelInterfaces ⊆
      PactType.ParallelInterfaces (PactType.par left right interface) := by
    intro message hMessage
    simp only [PactType.ParallelInterfaces, Finset.mem_union]
    exact Or.inl (Or.inr hMessage)
  have hRightSubset : right.ParallelInterfaces ⊆
      PactType.ParallelInterfaces (PactType.par left right interface) := by
    intro message hMessage
    simp only [PactType.ParallelInterfaces, Finset.mem_union]
    exact Or.inr hMessage
  have hOuterAvoidsLeft := hOuterAvoids.mono hLeftSubset
  have hOuterAvoidsRight := hOuterAvoids.mono hRightSubset
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftState rightState
      hLeftRelated hRightRelated =>
      cases hTargetRelated with
      | parallel _ _ leftTarget rightTarget _ leftTargetState
          rightTargetState hLeftTargetRelated hRightTargetRelated =>
          rcases (compileTypeFuel_parallel_hasResolvedEdge_iff signature
              left right interface leftState rightState leftTargetState
              rightTargetState environment label
              { current := current, future := future }).mp hEdge with
            ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
              leftSummary, rightSummary, hLeftEdge, hRightEdge,
              hSynchronized, hCombinedEnvironment, hLabel, hCurrent,
              hFuture⟩
          let leftAutomatonEdge : AutomatonFragmentEdge :=
            { source := leftState
              environment := leftEnvironment
              label := .visible leftLabel
              current := leftSummary.current
              future := leftSummary.future
              target := leftTargetState }
          let rightAutomatonEdge : AutomatonFragmentEdge :=
            { source := rightState
              environment := rightEnvironment
              label := .visible rightLabel
              current := rightSummary.current
              future := rightSummary.future
              target := rightTargetState }
          change syncAutomatonEdges interface
              (semanticResolvedAutomatonEdges (compileTypeFuel signature
                (typeCompilationFuel left) left))
              (semanticResolvedAutomatonEdges (compileTypeFuel signature
                (typeCompilationFuel right) right))
              leftAutomatonEdge rightAutomatonEdge at hSynchronized
          rcases hSynchronized with ⟨leftWitnessEdge, hLeftWitnessSemantic,
            rightWitnessEdge, hRightWitnessSemantic, hWitnessSync⟩
          have hLocalEnvironments :=
            TypeAlphabet.localEnvironments_of_syncAutomatonEdgeWitnesses_local
              signature interface hInterface hOuterEnvironment
              hCombinedEnvironment hWitnessSync
          have hLeftAvoidsPair :=
            syncAutomatonEdgeWitnesses_environments_avoid interface
              left.ParallelInterfaces hCombinedEnvironment hOuterAvoidsLeft
              hDisjointLeft hWitnessSync
          have hRightAvoidsPair :=
            syncAutomatonEdgeWitnesses_environments_avoid interface
              right.ParallelInterfaces hCombinedEnvironment hOuterAvoidsRight
              hDisjointRight hWitnessSync
          rcases (hLeftStep hLeftRelated hLocalEnvironments.1
              hLeftAvoidsPair.1).mpr
              ⟨leftTargetState, hLeftEdge, hLeftTargetRelated⟩ with
            ⟨hLeftTransition, hLeftOffers⟩
          rcases (hRightStep hRightRelated hLocalEnvironments.2
              hRightAvoidsPair.2).mpr
              ⟨rightTargetState, hRightEdge, hRightTargetRelated⟩ with
            ⟨hRightTransition, hRightOffers⟩
          have hWitnessFields := hWitnessSync
          unfold syncAutomatonEdgeWitnesses at hWitnessFields
          rcases hWitnessFields with ⟨hLeftMatch, hRightMatch, _,
            hLabelSyncRaw⟩
          have hLeftWitnessEdge : leftWitnessEdge ∈ resolvedAutomatonEdges
              (compileTypeFuel signature (typeCompilationFuel left) left) :=
            (Finset.mem_filter.mp hLeftWitnessSemantic).1
          have hRightWitnessEdge : rightWitnessEdge ∈ resolvedAutomatonEdges
              (compileTypeFuel signature (typeCompilationFuel right) right) :=
            (Finset.mem_filter.mp hRightWitnessSemantic).1
          obtain ⟨leftWitnessTarget, hLeftWitnessOffers⟩ :=
            hLeftWitness hLeftRelated hLocalEnvironments.1
              hLeftAvoidsPair.1 hLeftEdge leftWitnessEdge hLeftWitnessEdge
              (Finset.mem_filter.mp hLeftWitnessSemantic).2 hLeftMatch.1
              hLeftMatch.2.1 hLeftMatch.2.2
          obtain ⟨rightWitnessTarget, hRightWitnessOffers⟩ :=
            hRightWitness hRightRelated hLocalEnvironments.2
              hRightAvoidsPair.2 hRightEdge rightWitnessEdge hRightWitnessEdge
              (Finset.mem_filter.mp hRightWitnessSemantic).2 hRightMatch.1
              hRightMatch.2.1 hRightMatch.2.2
          have hLeftWitnessOffers' : TypeOffers leftWitnessEdge.environment
              leftResidual leftWitnessEdge.label.semantic leftWitnessTarget
              leftWitnessEdge.current leftWitnessEdge.future := by
            rw [hLeftMatch.2.1, hLeftMatch.2.2]
            exact hLeftWitnessOffers
          have hRightWitnessOffers' : TypeOffers rightWitnessEdge.environment
              rightResidual rightWitnessEdge.label.semantic rightWitnessTarget
              rightWitnessEdge.current rightWitnessEdge.future := by
            rw [hRightMatch.2.1, hRightMatch.2.2]
            exact hRightWitnessOffers
          have hSemanticLocals :=
            syncAutomatonEdgeWitnesses_to_localTypeEnvironments interface
              hLeftWitnessOffers' hRightWitnessOffers' hWitnessSync
          dsimp only at hSemanticLocals
          have hSemanticLocals' :
              LocalTypeEnvironment environment interface rightEnvironment
                  rightResidual rightLabel leftEnvironment ∧
                LocalTypeEnvironment environment interface leftEnvironment
                  leftResidual leftLabel rightEnvironment := by
            simpa [leftAutomatonEdge, rightAutomatonEdge,
              hCombinedEnvironment] using hSemanticLocals
          have hLabelSync : TypeLabel.Sync interface leftLabel rightLabel := by
            simpa [leftAutomatonEdge, rightAutomatonEdge,
              AutomatonConstructionLabel.semantic] using hLabelSyncRaw
          have hEnvironmentWellFormed : environment.WellFormed :=
            signature.localEnvironment_wellFormed hOuterEnvironment
          have hParentTransition := TypeTransition.par environment
            leftEnvironment rightEnvironment interface leftResidual leftTarget
            rightResidual rightTarget leftLabel rightLabel hLeftTransition
            hRightTransition ⟨hEnvironmentWellFormed, hSemanticLocals'.1,
              hSemanticLocals'.2, hLabelSync⟩
          have hParentOffers := TypeOffers.par environment leftEnvironment
            rightEnvironment interface leftResidual leftTarget rightResidual
            rightTarget leftLabel rightLabel leftSummary.current
            leftSummary.future rightSummary.current rightSummary.future
            hLeftOffers hRightOffers hSemanticLocals'.1 hSemanticLocals'.2
            ⟨hEnvironmentWellFormed, hLabelSync⟩
          constructor
          · simpa [hLabel] using hParentTransition
          · change TypeOffers environment
              (.par leftResidual rightResidual interface) label
              (.par leftTarget rightTarget interface) current future
            have hCurrent' : hideOffers interface
                (leftSummary.current ∪ rightSummary.current) = current := by
              simpa using hCurrent
            have hFuture' : hideOffers interface
                (leftSummary.future ∪ rightSummary.future) = future := by
              simpa using hFuture
            rw [← hCurrent', ← hFuture']
            simpa [hideOffers, hideTypeOffers, hLabel] using hParentOffers

/-- Target relatedness composes through the synchronized product.  Internal
future-observation self-loops cannot appear in `HasResolvedEdge`; every such
edge therefore has a pair target assembled from two visible child edges. -/
theorem compilationResolvedEdgeTargetsRelated_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature
      (.par left right interface) := by
  classical
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftSource rightSource
      hLeftRelated hRightRelated =>
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
      have hFragment : compileTypeFuel signature
          (typeCompilationFuel (.par left right interface))
          (.par left right interface) =
          buildParallelAutomaton interface leftFragment rightFragment := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      have hOriginal := hEdge
      rw [hFragment] at hEdge
      rcases hEdge with ⟨pending, hPending, hSource, hEnvironment, hLabel,
        hCurrent, hFuture, hTarget⟩
      simp only [buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_filter] at hPending
      rcases hPending with hTransition | hObservation
      · rcases hTransition with
          ⟨leftEdge, hLeftMember, rightEdge, hRightMember, rfl⟩
        simp only at hSource hTarget
        injection hSource with hLeftSource hRightSource
        have hTargetEq : target = .pair leftEdge.target rightEdge.target :=
          hTarget.symm
        subst target
        rcases (compileTypeFuel_parallel_hasResolvedEdge_iff signature left
            right interface leftSource rightSource leftEdge.target
            rightEdge.target environment label offers).mp hOriginal with
          ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
            leftOffers, rightOffers, hLeftEdge, hRightEdge, _⟩
        rcases hLeftTargets hLeftRelated hLeftEdge with
          ⟨leftTargetResidual, hLeftTargetRelated⟩
        rcases hRightTargets hRightRelated hRightEdge with
          ⟨rightTargetResidual, hRightTargetRelated⟩
        exact ⟨.par leftTargetResidual rightTargetResidual interface,
          TypeCompilationRelation.parallel left right leftTargetResidual
            rightTargetResidual interface leftEdge.target rightEdge.target
            hLeftTargetRelated hRightTargetRelated⟩
      · rcases hObservation with hLeftObservation | hRightObservation
        · rcases hLeftObservation with ⟨leftState, _, rightState, _, rfl⟩
          simp at hLabel
        · rcases hRightObservation with ⟨leftState, _, rightState, _, rfl⟩
          simp at hLabel

private theorem resolvedAutomatonEdge_label_visible_of_pendingEdgesVisible
    (fragment : AutomatonFragment)
    (hVisible : ∀ edge ∈ fragment.edges,
      edge.label ≠ .future → ∃ label, edge.label = .visible label)
    {edge : AutomatonFragmentEdge}
    (hEdge : edge ∈ resolvedAutomatonEdges fragment)
    (hSemantic : edge.label ≠ .future) :
    ∃ label, edge.label = .visible label := by
  classical
  simp only [resolvedAutomatonEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨pending, hPending, hResolved⟩
  have hPendingSemantic : pending.label ≠ .future := by
    intro hFuture
    apply hSemantic
    have hResolvedLabel := congrArg AutomatonFragmentEdge.label hResolved
    simpa [hFuture] using hResolvedLabel.symm
  obtain ⟨label, hLabel⟩ := hVisible pending hPending hPendingSemantic
  refine ⟨label, ?_⟩
  have hResolvedLabel := congrArg AutomatonFragmentEdge.label hResolved
  simpa [hLabel] using hResolvedLabel.symm

/-- Scoped step correctness, target relatedness, and elimination of temporary
variable markers together realize every independently selected resolved offer
witness used by a synchronized product. -/
theorem compilationScopedResolvedOfferWitnessCorrect_of_step_targets_visible
    (signature : TypeAlphabet) (processType : PactType)
    (hStep : CompilationScopedFragmentStepCorrect signature processType)
    (hTargets : CompilationResolvedEdgeTargetsRelated signature processType)
    (hVisible : CompilationPendingEdgesVisible signature processType) :
    CompilationScopedResolvedOfferWitnessCorrect signature processType := by
  intro residual state environment label actualOffers actualTarget hRelated
    hLocalEnvironment hAvoids hActualEdge witness hWitness hWitnessSemantic
    hSource hEnvironment hLabel
  obtain ⟨witnessLabel, hWitnessLabel⟩ :=
    resolvedAutomatonEdge_label_visible_of_pendingEdgesVisible _ hVisible
      hWitness hWitnessSemantic
  have hSemanticLabel : witnessLabel = label := by
    have hSemantic := hLabel
    rw [hWitnessLabel] at hSemantic
    simpa [AutomatonConstructionLabel.semantic] using hSemantic
  let witnessOffers : TypeOfferSummary :=
    { current := witness.current, future := witness.future }
  have hWitnessResolved : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature (typeCompilationFuel processType) processType)
      state environment label witnessOffers witness.target := by
    apply (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mp
    let witnessShape : AutomatonFragmentEdge :=
      { source := state
        environment := environment
        label := .visible label
        current := witness.current
        future := witness.future
        target := witness.target }
    have hWitnessShape : witnessShape = witness := by
      cases witness
      simp_all [witnessShape]
    change witnessShape ∈ resolvedAutomatonEdges
      (compileTypeFuel signature (typeCompilationFuel processType) processType)
    rw [hWitnessShape]
    exact hWitness
  obtain ⟨targetResidual, hTargetRelated⟩ :=
    hTargets hRelated hWitnessResolved
  have hDecorated := (hStep hRelated hLocalEnvironment hAvoids).mpr
    ⟨witness.target, hWitnessResolved, hTargetRelated⟩
  exact ⟨targetResidual, hDecorated.2⟩
end

end Pact
