import Anvilpp.PactTypes.NewCorrespondence.Helpers.ChoiceRelations

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def seqRelationShape
    (signature : TypeAlphabet) (left right : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 residualLeft, entry = (.seq residualLeft right, .child 0 q1) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1) ∨
    (∃ q2, entry.2 = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        entry.1 q2)

/-- Proves the sufficient-fuel sequence fragment is the sequence builder applied to the sufficient child fragments. -/
theorem compileTypeFuel_sequence_eq_build
    (signature : TypeAlphabet) (left right : PactType) :
    compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right) =
      buildSequenceAutomaton signature
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right) := by
  have hFuelEq : typeCompilationFuel (.seq left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  show buildSequenceAutomaton signature
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right) =
    buildSequenceAutomaton signature
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
  rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
    compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]

/-- Proves sequence edges leaving a right-child state are exactly copied right-child edges. -/
theorem buildSequenceAutomaton_outgoing_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    edge ∈ (buildSequenceAutomaton signature left right).edges ∧
        edge.source = .child 1 state ↔
      ∃ childEdge ∈ right.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      childPendingEdges, sequenceEntryBridgeEdges,
      sequenceCompletingBridgeEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((hLeft | hRight) | hEntry) | hCompleting
    · rcases hLeft with ⟨childEdge, _hChildEdge, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [sequenceLeftEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, hChildEdge, hEdgeEq⟩
      have hChildSource := hSource
      rw [← hEdgeEq] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdgeEq.symm⟩
    · split at hEntry
      · simp only [Finset.mem_image] at hEntry
        rcases hEntry with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childState] at hSource
      · simp at hEntry
    · rcases hCompleting with ⟨source, _hSource, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSequenceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨childEdge, hChildEdge, rfl⟩))
    · simp [childPendingEdge, childState, hChildSource]

private theorem buildSequenceAutomaton_referencedStates_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.referencedStates (.child 1 state) =
      (child.referencedStates state).image (.child 1) := by
  classical
  ext target
  constructor
  · intro hTarget
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter] at hTarget
    rcases hTarget with ⟨edge, ⟨hEdgeMem, hEdgeSource⟩, hReference⟩
    obtain ⟨childEdge, hChildEdgeMem, hChildSource, hEdgeEq⟩ :=
      (buildSequenceAutomaton_outgoing_right signature left right state edge).mp
        ⟨hEdgeMem, hEdgeSource⟩
    subst edge
    by_cases hTock : childEdge.label.semantic = TypeLabel.tock
    · simp [childPendingEdge, hTock] at hReference
    · cases hFuture : childEdge.future with
      | explicit offers =>
          simp [childPendingEdge, childFutureSpec, hTock, hFuture] at hReference
      | «at» childTarget removed =>
          have hTargetEq : target = childState 1 childTarget := by
            simpa [childPendingEdge, childFutureSpec, childState, hTock,
              hFuture] using hReference
          apply Finset.mem_image.mpr
          refine ⟨childTarget, ?_, hTargetEq.symm⟩
          simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
            Finset.mem_filter]
          refine ⟨childEdge, ⟨hChildEdgeMem, hChildSource⟩, ?_⟩
          simp [hTock, hFuture]
  · intro hTarget
    rcases Finset.mem_image.mp hTarget with
      ⟨childTarget, hChildTarget, hTargetEq⟩
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter] at hChildTarget ⊢
    rcases hChildTarget with
      ⟨childEdge, ⟨hChildEdgeMem, hChildSource⟩, hChildReference⟩
    refine ⟨childPendingEdge 1 childEdge, ?_, ?_⟩
    · exact (buildSequenceAutomaton_outgoing_right signature left right state
        (childPendingEdge 1 childEdge)).mpr
          ⟨childEdge, hChildEdgeMem, hChildSource, rfl⟩
    · rw [← hTargetEq]
      cases hFuture : childEdge.future with
      | explicit offers =>
          by_cases hTock : childEdge.label.semantic = TypeLabel.tock
          · simp [hTock] at hChildReference
          · simp [hTock, hFuture] at hChildReference
      | «at» referencedTarget removed =>
          by_cases hTock : childEdge.label.semantic = TypeLabel.tock
          · simp [hTock] at hChildReference
          · have hChildEq : childTarget = referencedTarget := by
              simpa [hTock, hFuture] using hChildReference
            have hTaggedEq := congrArg (childState 1) hChildEq
            simpa [childPendingEdge, childFutureSpec, childState, hTock,
              hFuture] using hTaggedEq

private theorem buildSequenceAutomaton_offersAt_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.offersAt (.child 1 state) = child.offersAt state := by
  classical
  ext action
  constructor
  · intro hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction ⊢
    rcases hAction with ⟨edge, ⟨hEdgeMem, hEdgeSource⟩, hOffer⟩
    obtain ⟨childEdge, hChildEdgeMem, hChildSource, hEdgeEq⟩ :=
      (buildSequenceAutomaton_outgoing_right signature left right state edge).mp
        ⟨hEdgeMem, hEdgeSource⟩
    subst edge
    refine ⟨childEdge, ⟨hChildEdgeMem, hChildSource⟩, ?_⟩
    cases hFuture : childEdge.future <;>
      simpa [childPendingEdge, childFutureSpec, childState, hFuture] using hOffer
  · intro hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction ⊢
    rcases hAction with
      ⟨childEdge, ⟨hChildEdgeMem, hChildSource⟩, hOffer⟩
    refine ⟨childPendingEdge 1 childEdge, ?_, ?_⟩
    · exact (buildSequenceAutomaton_outgoing_right signature left right state
        (childPendingEdge 1 childEdge)).mpr
          ⟨childEdge, hChildEdgeMem, hChildSource, rfl⟩
    · cases hFuture : childEdge.future <;>
        simpa [childPendingEdge, childFutureSpec, childState, hFuture] using hOffer

/-- Proves a `.child 1`-tagged state's future menu, in a compiled sequence, agrees with the right child's own. -/
theorem computeFutureOf_sequence_right
    (signature : TypeAlphabet) (left right : PactType)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel right)
      right).states) :
    computeFutureOf signature (.seq left right) (.child 1 state) =
      computeFutureOf signature right state := by
  classical
  let leftFragment :=
    compileTypeFuel signature (typeCompilationFuel left) left
  let rightFragment :=
    compileTypeFuel signature (typeCompilationFuel right) right
  let sequence := buildSequenceAutomaton signature leftFragment rightFragment
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let child : PendingAutomaton :=
    { states := rightFragment.states, edges := rightFragment.edges }
  have hCard : child.states.card ≤ parent.states.card := by
    have hTaggedCard :
        (childStates 1 rightFragment).card = rightFragment.states.card := by
      unfold childStates
      apply Finset.card_image_of_injective
      intro first second hEq
      simpa [childState] using hEq
    change rightFragment.states.card ≤ sequence.states.card
    rw [← hTaggedCard]
    apply Finset.card_le_card
    intro tagged hTagged
    simp only [sequence, buildSequenceAutomaton, finishAutomatonFragment,
      Finset.mem_union]
    exact Or.inr hTagged
  have hReachable :
      parent.futureReachable (.child 1 state) =
        (child.futureReachable state).image (.child 1) := by
    apply PendingAutomaton.futureReachable_eq_of_embedding child parent (.child 1)
    · exact buildSequenceAutomaton_referencedStates_right signature
        leftFragment rightFragment
    · exact compileTypeFuel_referencesClosed signature
        (typeCompilationFuel right) right le_rfl
    · simpa [child, rightFragment] using hState
    · exact hCard
  have hSequenceFuel : typeCompilationFuel (.seq left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  obtain ⟨rightFuel, hRightFuel⟩ :
      ∃ fuel, typeCompilationFuel right = fuel + 1 := by
    have hPositive := typeCompilationFuel_positive right
    exact ⟨typeCompilationFuel right - 1, by omega⟩
  unfold computeFutureOf
  rw [hSequenceFuel]
  conv_lhs => rw [computeFutureOfFuel]
  rw [hRightFuel]
  conv_rhs => rw [computeFutureOfFuel]
  rw [compileTypeFuel_sequence_eq_build]
  change (parent.futureReachable (.child 1 state)).biUnion _ =
    (child.futureReachable state).biUnion _
  rw [hReachable, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro visited _hVisited
  have hOffers := buildSequenceAutomaton_offersAt_right signature
    leftFragment rightFragment visited
  change parent.offersAt (.child 1 visited) = child.offersAt visited at hOffers
  rw [hOffers]
  have hInfo :
      stateProductInfo (.seq left right) (.child 1 visited) =
        stateProductInfo right visited := by
    unfold stateProductInfo
    rw [hSequenceFuel]
    simp only [stateProductInfoFuel]
    exact stateProductInfoFuel_eq_of_sufficient right visited
      (le_max_right _ _) le_rfl
  rw [hInfo]
  cases hProduct : stateProductInfo right visited with
  | none => rfl
  | some info =>
      rcases info with ⟨interface, productLeft, productRight, q1, q2⟩
      have hProductFuel :
          stateProductInfoFuel (typeCompilationFuel right) right visited =
            some (interface, productLeft, productRight, q1, q2) := by
        simpa [stateProductInfo] using hProduct
      obtain ⟨hLeftLt, hRightLt⟩ :=
        stateProductInfoFuel_component_fuel_lt
          (typeCompilationFuel right) right visited interface productLeft
          productRight q1 q2 (typeCompilationFuel_sufficient right)
          hProductFuel
      have hLeftSmall :
          TypeCompilationFuelSufficient productLeft rightFuel := by
        simp [TypeCompilationFuelSufficient] at hLeftLt ⊢
        omega
      have hRightSmall :
          TypeCompilationFuelSufficient productRight rightFuel := by
        simp [TypeCompilationFuelSufficient] at hRightLt ⊢
        omega
      have hLeftLarge : TypeCompilationFuelSufficient productLeft
          (max (typeCompilationFuel left) (rightFuel + 1)) := by
        exact le_trans hLeftSmall (le_trans (Nat.le_succ rightFuel)
          (le_max_right _ _))
      have hRightLarge : TypeCompilationFuelSufficient productRight
          (max (typeCompilationFuel left) (rightFuel + 1)) := by
        exact le_trans hRightSmall (le_trans (Nat.le_succ rightFuel)
          (le_max_right _ _))
      simp only
      rw [computeFutureOfFuel_eq_of_sufficient signature productLeft q1
          hLeftLarge hLeftSmall,
        computeFutureOfFuel_eq_of_sufficient signature productRight q2
          hRightLarge hRightSmall]

/-- Proves visible sequence edges leaving a left-child state are either rewritten left edges or the entry bridge. -/
theorem buildSequenceAutomaton_outgoing_left_visible
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge)
    {label : TypeLabel}
    (hVisible : edge.label = .visible label)
    (hOutgoing :
      edge ∈ (buildSequenceAutomaton signature left right).edges ∧
        edge.source = .child 0 state) :
    (∃ childEdge ∈ left.edges,
        childEdge.source = state ∧
          edge = sequenceLeftEdge left right childEdge) ∨
      (state = left.initial ∧ left.initial ∈ left.accepting ∧
        ∃ environment ∈ signature.localEnvironments,
          environment.clock = false ∧
            edge =
              { source := childState 0 left.initial
                environment := environment
                label := .visible TypeLabel.silent
                current := ∅
                future := .at (childState 1 right.initial) ∅
                target := childState 1 right.initial }) := by
  classical
  rcases hOutgoing with ⟨hEdge, hSource⟩
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    childPendingEdges, sequenceCompletingBridgeEdges, Finset.mem_union,
    Finset.mem_image] at hEdge
  rcases hEdge with ((hLeft | hRight) | hEntry) | hCompleting
  · rcases hLeft with ⟨childEdge, hChildEdge, hEdgeEq⟩
    have hChildSource := hSource
    rw [← hEdgeEq] at hChildSource
    simp [sequenceLeftEdge, childState] at hChildSource
    exact Or.inl ⟨childEdge, hChildEdge, hChildSource, hEdgeEq.symm⟩
  · rcases hRight with ⟨childEdge, _hChildEdge, hEdgeEq⟩
    rw [← hEdgeEq] at hSource
    simp [childPendingEdge, childState] at hSource
  · by_cases hAccepting : left.initial ∈ left.accepting
    · simp [sequenceEntryBridgeEdges, hAccepting, Finset.mem_image,
        Finset.mem_filter] at hEntry
      rcases hEntry with ⟨environment, hEnvironment, hEdgeEq⟩
      have hStateEq := hSource
      rw [← hEdgeEq] at hStateEq
      simp [childState] at hStateEq
      exact Or.inr ⟨hStateEq.symm, hAccepting, environment, hEnvironment.1,
        hEnvironment.2, hEdgeEq.symm⟩
    · simp [sequenceEntryBridgeEdges, hAccepting] at hEntry
  · rcases hCompleting with ⟨source, _hSource, hEdgeEq⟩
    have hLabel := hVisible
    rw [← hEdgeEq] at hLabel
    simp at hLabel

/-- Proves H15's future agreement for a retained left target of a sequence step. -/
lemma helper_h15_sequence_left_step_future_offers_agree
    (signature : TypeAlphabet) (left right : PactType)
    {leftTarget : PactType} {q' : TypeAutomatonState}
    (hTarget :
      relationMembership (buildRelationSet left (compileType signature left))
        leftTarget q')
    (hNonFinal : leftTarget ≠ .skip) :
    computeFutureOf signature (.seq left right) (.child 0 q') =
      typeFutureOffers (.seq leftTarget right) := by
  sorry

/-- Proves H15's future agreement for the right entry reached by a fused sequence step. -/
lemma helper_h15_sequence_left_fuse_future_offers_agree
    (signature : TypeAlphabet) (left right : PactType)
    {q' : TypeAutomatonState}
    (_hTarget :
      relationMembership (buildRelationSet left (compileType signature left))
        .skip q') :
    computeFutureOf signature (.seq left right)
        (.child 1 (compileType signature right).initial) =
      typeFutureOffers right := by
  rw [computeFutureOf_sequence_right signature left right
    (compileType signature right).initial
    (by
      show (compileTypeFuel signature (typeCompilationFuel right) right).initial ∈
        (compileTypeFuel signature (typeCompilationFuel right) right).states
      exact compileTypeFuel_initial_mem signature (typeCompilationFuel right)
        right le_rfl)]
  exact helper_h15_future_offers_agree signature
    (buildRelationSet_initial right (compileType signature right))

/-- Proves H15's future agreement for a right-child target of a sequence step. -/
lemma helper_h15_sequence_right_future_offers_agree
    (signature : TypeAlphabet) (left right : PactType)
    {rightTarget : PactType} {q' : TypeAutomatonState}
    (hTarget :
      relationMembership (buildRelationSet right (compileType signature right))
        rightTarget q') :
    computeFutureOf signature (.seq left right) (.child 1 q') =
      typeFutureOffers rightTarget := by
  sorry

/-- Describes the two semantic forms of a decorated sequence step. -/
inductive SeqDecoratedStepCase
    (right : PactType) (source target : PactType)
    (env : TypeEnvironment) (label : TypeLabel)
    (current future : Finset BareMessage) : Prop where
  | step (leftTarget : PactType) (childFuture : Finset BareMessage) :
      target = .seq leftTarget right →
      leftTarget ≠ .skip →
      DecoratedTypeTransition env source label
        (TypeOfferSummary.mk current childFuture) leftTarget →
      future = typeFutureOffers (.seq leftTarget right) \ current →
      SeqDecoratedStepCase right source target env label current future
  | fuse (childFuture : Finset BareMessage) :
      target = right →
      DecoratedTypeTransition env source label
        (TypeOfferSummary.mk current childFuture) .skip →
      future = typeFutureOffers right \ current →
      SeqDecoratedStepCase right source target env label current future

/-- Proves that every decorated sequence step is either retained on the left or fused into the right operand. -/
theorem decoratedTypeTransition_seq_cases
    {env : TypeEnvironment} {label : TypeLabel}
    {left right target : PactType}
    {current future : Finset BareMessage}
    (hStep :
      DecoratedTypeTransition env (.seq left right) label
        (TypeOfferSummary.mk current future) target) :
    SeqDecoratedStepCase right left target env label current future := by
  rcases hStep with ⟨hTransition, hOffers⟩
  cases hTransition with
  | seq_fuse env left right label hChildTransition =>
      have hChildOffers :
          ∃ childFuture,
            TypeOffers env left label .skip current childFuture ∧
              future = typeFutureOffers right \ current := by
        change TypeOffers env (.seq left right) label right current future at hOffers
        cases hOffers
        aesop
      rcases hChildOffers with ⟨childFuture, hChildOffers, hFuture⟩
      exact SeqDecoratedStepCase.fuse childFuture rfl
        ⟨hChildTransition, hChildOffers⟩ hFuture
  | seq env left leftTarget right label hChildTransition hNonFinal =>
      have hChildOffers :
          ∃ childFuture,
            TypeOffers env left label leftTarget current childFuture ∧
              future = typeFutureOffers (.seq leftTarget right) \ current := by
        change TypeOffers env (.seq left right) label (.seq leftTarget right)
          current future at hOffers
        cases hOffers
        aesop
      rcases hChildOffers with ⟨childFuture, hChildOffers, hFuture⟩
      exact SeqDecoratedStepCase.step leftTarget childFuture rfl hNonFinal
        ⟨hChildTransition, hChildOffers⟩ hFuture

/-- Describes the public edge families leaving a related compiled sequence state. -/
inductive SeqCompiledEdgeCase
    (signature : TypeAlphabet) (left right : PactType)
    (residual residual' : PactType)
    (state state' : TypeAutomatonState)
    (env : TypeEnvironment) (label : TypeLabel)
    (current future : Finset BareMessage) : Prop where
  | leftStep (leftResidual leftTarget : PactType)
      (q q' : TypeAutomatonState) (childFuture : Finset BareMessage) :
      residual = .seq leftResidual right →
      residual' = .seq leftTarget right →
      state = .child 0 q →
      state' = .child 0 q' →
      leftTarget ≠ .skip →
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q →
      relationMembership (buildRelationSet left (compileType signature left))
        leftTarget q' →
      (compileType signature left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q' →
      future = typeFutureOffers (.seq leftTarget right) \ current →
      SeqCompiledEdgeCase signature left right residual residual' state state'
        env label current future
  | leftFuse (leftResidual : PactType)
      (q q' : TypeAutomatonState) (childFuture : Finset BareMessage) :
      residual = .seq leftResidual right →
      residual' = right →
      state = .child 0 q →
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q →
      relationMembership (buildRelationSet left (compileType signature left))
        .skip q' →
      (compileType signature left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q' →
      future = typeFutureOffers right \ current →
      SeqCompiledEdgeCase signature left right residual residual' state state'
        env label current future
  | entryFuse :
      residual = .seq .skip right →
      residual' = right →
      state = .child 0 (compileType signature left).initial →
      state' = .child 1 (compileType signature right).initial →
      label = TypeLabel.silent →
      current = ∅ →
      future = typeFutureOffers right →
      env.WellFormed →
      env.clock = false →
      SeqCompiledEdgeCase signature left right residual residual' state state'
        env label current future
  | rightStep (q q' : TypeAutomatonState) :
      state = .child 1 q →
      state' = .child 1 q' →
      relationMembership (buildRelationSet right (compileType signature right))
        residual q →
      relationMembership (buildRelationSet right (compileType signature right))
        residual' q' →
      (compileType signature right).HasEdge q env label
        (TypeOfferSummary.mk current future) q' →
      SeqCompiledEdgeCase signature left right residual residual' state state'
        env label current future

/-- Proves a public edge from the left side of a sequence is retained or fused according to the child target. -/
lemma helper_h15_sequence_left_public_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {leftResidual residual' : PactType}
    {q state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        (.seq leftResidual right) (.child 0 q))
    (hLeftSource :
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q)
    (hEdge :
      (compileType signature (.seq left right)).HasEdge (.child 0 q) env label
        (TypeOfferSummary.mk current future) state')
    (hTarget :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        residual' state') :
    SeqCompiledEdgeCase signature left right (.seq leftResidual right) residual'
      (.child 0 q) state' env label current future := by
  have hFutureEq :
      future = typeFutureOffers residual' \ current :=
    helper_h15_edge_future_offers_agree signature hParentSource hTarget hEdge
  sorry

/-- Lifts a non-final left-child edge to a retained public sequence edge. -/
theorem compileType_seq_lift_left_step
    (signature : TypeAlphabet) (left right : PactType)
    {leftResidual leftTarget : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current childFuture : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        (.seq leftResidual right) (.child 0 q))
    (_hSource :
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q)
    (hTarget :
      relationMembership (buildRelationSet left (compileType signature left))
        leftTarget q')
    (hNonFinal : leftTarget ≠ .skip)
    (hChildStep :
      DecoratedTypeTransition env leftResidual label
        (TypeOfferSummary.mk current childFuture) leftTarget)
    (hParentSymbol :
      TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq leftTarget right) \ current)) ∈
        signature.transitionAlphabet)
    (hChildEdge :
      (compileType signature left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q') :
    (compileType signature (.seq left right)).HasEdge (.child 0 q) env label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq leftTarget right) \ current)) (.child 0 q') ∧
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        (.seq leftTarget right) (.child 0 q') := by
  have hChildSymbol := compileType_hasEdge_symbol_mem signature left hChildEdge
  have hChildResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature left q q' env label
      (TypeOfferSummary.mk current childFuture) hChildSymbol).mp hChildEdge
  rcases hChildResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, _hPendingFuture,
    hPendingTarget⟩
  have hNotAccepting :
      q' ∉ (compileTypeFuel signature (typeCompilationFuel left) left).accepting := by
    intro hAccepting
    have hAccepting' : q' ∈ (compileType signature left).accepting := by
      simpa [compileType] using hAccepting
    exact hNonFinal
      ((helper_h13_final_states_represent_completion signature hTarget).mp
        hAccepting')
  have hSeqFuture :=
    helper_h15_sequence_left_step_future_offers_agree signature left right
      hTarget hNonFinal
  have hParentEdge :
      (compileType signature (.seq left right)).HasEdge (.child 0 q) env label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq leftTarget right) \ current))
        (.child 0 q') := by
    rw [compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
      (.child 0 q) (.child 0 q') env label
      (TypeOfferSummary.mk current
        (typeFutureOffers (.seq leftTarget right) \ current)) hParentSymbol]
    rw [compileTypeFuel_sequence_eq_build signature left right]
    refine ⟨sequenceLeftEdge
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
      pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl ⟨pendingEdge, hPendingMem, rfl⟩))
    · simp [sequenceLeftEdge, childState, hPendingSource]
    · simp [sequenceLeftEdge, hPendingEnv]
    · simp [sequenceLeftEdge, hPendingLabel]
    · simp [sequenceLeftEdge, hPendingCurrent]
    · have hSeqFuture' :
          computeFutureOf signature (.seq left right) (childState 0 q') =
            typeFutureOffers (.seq leftTarget right) := by
        simpa [childState] using hSeqFuture
      simp [sequenceLeftEdge, hPendingLabel, hPendingCurrent,
        hPendingTarget, sequenceRedirect_of_not_accepting hNotAccepting,
        hSeqFuture']
    · simp [sequenceLeftEdge, childState, hPendingTarget,
        sequenceRedirect_of_not_accepting hNotAccepting]
  have hParentStep :
      DecoratedTypeTransition env (.seq leftResidual right) label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq leftTarget right) \ current))
        (.seq leftTarget right) :=
    ⟨TypeTransition.seq env leftResidual leftTarget right label hChildStep.1
        hNonFinal,
      TypeOffers.seq env leftResidual leftTarget right label current childFuture
        hChildStep.2 hNonFinal⟩
  refine ⟨hParentEdge, ?_⟩
  exact relationMembership_of_step_edge_unique (.seq left right)
    (compileType signature (.seq left right)) hParentSource hParentEdge
    hParentStep
    (fun target hTargetStep =>
      decoratedTypeTransition_target_unique hTargetStep hParentStep)

/-- Lifts a final left-child edge to the redirected public sequence edge. -/
theorem compileType_seq_lift_left_fuse
    (signature : TypeAlphabet) (left right : PactType)
    {leftResidual : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current childFuture : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        (.seq leftResidual right) (.child 0 q))
    (_hSource :
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q)
    (hTarget :
      relationMembership (buildRelationSet left (compileType signature left))
        .skip q')
    (hChildStep :
      DecoratedTypeTransition env leftResidual label
        (TypeOfferSummary.mk current childFuture) .skip)
    (hParentSymbol :
      TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current)) ∈
        signature.transitionAlphabet)
    (hChildEdge :
      (compileType signature left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q') :
    (compileType signature (.seq left right)).HasEdge (.child 0 q) env label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current))
        (.child 1 (compileType signature right).initial) ∧
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        right (.child 1 (compileType signature right).initial) := by
  have hChildSymbol := compileType_hasEdge_symbol_mem signature left hChildEdge
  have hChildResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature left q q' env label
      (TypeOfferSummary.mk current childFuture) hChildSymbol).mp hChildEdge
  rcases hChildResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, _hPendingFuture,
    hPendingTarget⟩
  have hAccepting :
      q' ∈ (compileTypeFuel signature (typeCompilationFuel left) left).accepting := by
    have hAccepting' : q' ∈ (compileType signature left).accepting :=
      (helper_h13_final_states_represent_completion signature hTarget).mpr rfl
    simpa [compileType] using hAccepting'
  have hSeqFuture :=
    helper_h15_sequence_left_fuse_future_offers_agree signature left right hTarget
  have hParentEdge :
      (compileType signature (.seq left right)).HasEdge (.child 0 q) env label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current))
        (.child 1 (compileType signature right).initial) := by
    rw [compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
      (.child 0 q) (.child 1 (compileType signature right).initial) env label
      (TypeOfferSummary.mk current (typeFutureOffers right \ current))
      hParentSymbol]
    rw [compileTypeFuel_sequence_eq_build signature left right]
    refine ⟨sequenceLeftEdge
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
      pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl ⟨pendingEdge, hPendingMem, rfl⟩))
    · simp [sequenceLeftEdge, childState, hPendingSource]
    · simp [sequenceLeftEdge, hPendingEnv]
    · simp [sequenceLeftEdge, hPendingLabel]
    · simp [sequenceLeftEdge, hPendingCurrent]
    · have hSeqFuture' :
          computeFutureOf signature (.seq left right)
              (childState 1
                (compileTypeFuel signature (typeCompilationFuel right) right).initial) =
            typeFutureOffers right := by
        simpa [compileType, childState] using hSeqFuture
      simp [sequenceLeftEdge, hPendingLabel, hPendingCurrent,
        hPendingTarget, sequenceRedirect_of_accepting hAccepting,
        hSeqFuture']
    · simp [sequenceLeftEdge, compileType, childState, hPendingTarget,
        sequenceRedirect_of_accepting hAccepting]
  have hParentStep :
      DecoratedTypeTransition env (.seq leftResidual right) label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current))
        right :=
    ⟨TypeTransition.seq_fuse env leftResidual right label hChildStep.1,
      TypeOffers.seq_fuse env leftResidual right label current childFuture
        hChildStep.2⟩
  refine ⟨hParentEdge, ?_⟩
  exact relationMembership_of_step_edge_unique (.seq left right)
    (compileType signature (.seq left right)) hParentSource hParentEdge
    hParentStep
    (fun target hTargetStep =>
      decoratedTypeTransition_target_unique hTargetStep hParentStep)

/-- Lifts a right-child edge to a copied public sequence edge. -/
theorem compileType_seq_lift_right_step
    (signature : TypeAlphabet) (left right : PactType)
    {rightResidual rightTarget : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        rightResidual (.child 1 q))
    (_hSource :
      relationMembership (buildRelationSet right (compileType signature right))
        rightResidual q)
    (_hTarget :
      relationMembership (buildRelationSet right (compileType signature right))
        rightTarget q')
    (hChildStep :
      DecoratedTypeTransition env rightResidual label offers rightTarget)
    (hChildEdge :
      (compileType signature right).HasEdge q env label offers q') :
    ∃ state',
      (compileType signature (.seq left right)).HasEdge (.child 1 q) env label
        offers state' ∧
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        rightTarget state' := by
  have hChildSymbol := compileType_hasEdge_symbol_mem signature right hChildEdge
  have hChildResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature right q q' env label
      offers hChildSymbol).mp hChildEdge
  rcases hChildResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, hPendingFuture,
    hPendingTarget⟩
  have hParentEdge :
      (compileType signature (.seq left right)).HasEdge (.child 1 q) env label
        offers (.child 1 q') := by
    rw [compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
      (.child 1 q) (.child 1 q') env label offers hChildSymbol]
    rw [compileTypeFuel_sequence_eq_build signature left right]
    refine ⟨childPendingEdge 1 pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨pendingEdge, hPendingMem, rfl⟩))
    · simp [childPendingEdge, childState, hPendingSource]
    · simp [childPendingEdge, hPendingEnv]
    · simp [childPendingEdge, hPendingLabel]
    · simp [childPendingEdge, hPendingCurrent]
    · cases hSpec : pendingEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using
            hPendingFuture
      | «at» futureTarget removed =>
          have hStateMem := compileTypeFuel_futureTargetsInStates signature
            (typeCompilationFuel right) right le_rfl pendingEdge hPendingMem
            futureTarget removed hSpec
          have hSeqFuture :=
            computeFutureOf_sequence_right signature left right futureTarget
              hStateMem
          have hSeqFuture' :
              computeFutureOf signature (.seq left right)
                  (childState 1 futureTarget) =
                computeFutureOf signature right futureTarget := by
            simpa [childState] using hSeqFuture
          simpa [childPendingEdge, childFutureSpec, hSpec, hSeqFuture'] using
            hPendingFuture
    · simp [childPendingEdge, childState, hPendingTarget]
  refine ⟨.child 1 q', hParentEdge, ?_⟩
  exact relationMembership_of_step_edge_unique (.seq left right)
    (compileType signature (.seq left right)) hParentSource hParentEdge
    hChildStep
    (fun target hTargetStep =>
      decoratedTypeTransition_target_unique hTargetStep hChildStep)

/-- Proves an automaton edge's target is uniquely determined by its full decorated symbol. -/
lemma compileType_hasEdge_target_unique
    (signature : TypeAlphabet) (processType : PactType)
    {source target target' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType signature processType).HasEdge source env label offers
      target)
    (hEdge' : (compileType signature processType).HasEdge source env label offers
      target') :
    target = target' := by
  sorry

/-- Proves every related sequence pair has the sequence shape, given the forward direction of the left child's own step correspondence. -/
lemma relationMembership_seq_cases
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftForward :
      ∀ {residual' : PactType} {q1 : TypeAutomatonState} {env : TypeEnvironment}
        {label : TypeLabel} {offers : TypeOfferSummary} {target : PactType},
        relationMembership (buildRelationSet left (compileType signature left))
          residual' q1 →
        (TypeAutomatonSymbol.mk env label offers ∈
          (compileType signature left).alphabet) →
        DecoratedTypeTransition env residual' label offers target →
        ∃ q1', (compileType signature left).HasEdge q1 env label offers q1' ∧
          relationMembership (buildRelationSet left (compileType signature left))
            target q1')
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        residual state) :
    seqRelationShape signature left right (residual, state) := by
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right) =
        buildSequenceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right) :=
    compileTypeFuel_sequence_eq_build signature left right
  have hInit : (compileType signature (.seq left right)).initial =
      .child 0 (compileType signature left).initial := by
    show (compileTypeFuel signature (typeCompilationFuel (.seq left right))
      (.seq left right)).initial = .child 0 (compileTypeFuel signature
        (typeCompilationFuel left) left).initial
    rw [hWhole]
    simp [buildSequenceAutomaton, finishAutomatonFragment, childState]
  have hResult :=
    buildRelationSet_preserves (.seq left right)
    (compileType signature (.seq left right))
    (fun entry =>
      relationMembership
        (buildRelationSet (.seq left right) (compileType signature (.seq left right)))
        entry.1 entry.2 ∧
      seqRelationShape signature left right entry)
    (by
      refine ⟨buildRelationSet_initial (.seq left right)
        (compileType signature (.seq left right)), ?_⟩
      show seqRelationShape signature left right
        (.seq left right, (compileType signature (.seq left right)).initial)
      rw [hInit]
      exact Or.inl ⟨(compileType signature left).initial, left, rfl,
        buildRelationSet_initial left (compileType signature left)⟩)
    (by
      intro entry hEntryAnd successor hSuccessor
      obtain ⟨hEntryMem, hEntry⟩ := hEntryAnd
      have hSuccessorMem :
          relationMembership
            (buildRelationSet (.seq left right)
              (compileType signature (.seq left right))) successor.1 successor.2 :=
        buildRelationSet_saturated (.seq left right)
          (compileType signature (.seq left right)) entry hEntryMem hSuccessor
      refine ⟨hSuccessorMem, ?_⟩
      rcases relationSuccessors_mem_cases (compileType signature (.seq left right))
        entry successor hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
      have hSymbolMem := compileType_hasEdge_symbol_mem signature (.seq left right)
        (show (compileType signature (.seq left right)).HasEdge edge.source
          edge.symbol.environment edge.symbol.label edge.symbol.offers edge.target
          from hEdgeMem)
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.seq left right) edge.source edge.target edge.symbol.environment
        edge.symbol.label edge.symbol.offers hSymbolMem).mp hEdgeMem
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      rcases hEntry with ⟨q1, residualLeft, hEntryEq, hMem⟩ | ⟨q2, hStateEq, hMem⟩
      · -- entry retains a left state, representing `residualLeft ; right`
        have hEntry1 : entry.1 = .seq residualLeft right := by rw [hEntryEq]
        have hEntry2 : entry.2 = .child 0 q1 := by rw [hEntryEq]
        have hParentSource :
            relationMembership
              (buildRelationSet (.seq left right)
                (compileType signature (.seq left right)))
              (.seq residualLeft right) (.child 0 q1) := by
          rw [← hEntry1, ← hEntry2]; exact hEntryMem
        rw [hEntry1] at hStep
        cases decoratedTypeTransition_seq_cases hStep with
        | step leftTarget childFuture hTargetEq' hNonFinal hChildStep hFutureEq =>
            -- Given a genuine left-child step, we need the left forward
            -- direction to find the matching left edge and target relation.
            have hOuterMem :
                TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
                    edge.symbol.offers ∈ signature.transitionAlphabet := by
              simpa [compileType] using hSymbolMem
            have hParentSymbol :
                TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
                    (TypeOfferSummary.mk edge.symbol.offers.current
                      (typeFutureOffers (.seq leftTarget right) \
                        edge.symbol.offers.current)) ∈
                  signature.transitionAlphabet := by
              rw [← hFutureEq]; exact hOuterMem
            have hChildSymbol :
                TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
                    (TypeOfferSummary.mk edge.symbol.offers.current childFuture) ∈
                  (compileType signature left).alphabet := by
              change TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
                  (TypeOfferSummary.mk edge.symbol.offers.current childFuture) ∈
                signature.transitionAlphabet
              refine transitionAlphabet_of_typeOffers_target_subset signature
                hOuterMem hChildStep.2 ?_
              rw [hFutureEq]
              exact typeFutureOffers_subset_sequence_left_sdiff_union
                leftTarget right edge.symbol.offers.current
            obtain ⟨q1', hChildEdge, hChildTargetRelated⟩ :=
              hLeftForward hMem hChildSymbol hChildStep
            obtain ⟨hParentEdge, -⟩ :=
              compileType_seq_lift_left_step signature left right hParentSource hMem
                hChildTargetRelated hNonFinal hChildStep hParentSymbol hChildEdge
            have hOuterEdge :
                (compileType signature (.seq left right)).HasEdge entry.2
                  edge.symbol.environment edge.symbol.label edge.symbol.offers
                  successor.2 := by
              rw [← hSource, hTarget]; exact hEdgeMem
            have hSuccessorEq : successor.2 = .child 0 q1' := by
              apply compileType_hasEdge_target_unique signature (.seq left right)
                hOuterEdge
              rw [hEntry2, show edge.symbol.offers = TypeOfferSummary.mk
                edge.symbol.offers.current edge.symbol.offers.future from rfl, hFutureEq]
              exact hParentEdge
            exact Or.inl ⟨q1', leftTarget, Prod.ext hTargetEq' hSuccessorEq,
              hChildTargetRelated⟩
        | fuse childFuture hTargetEq' hChildStep hFutureEq =>
            -- Given a fused left-child step, we need the left forward
            -- direction to find the matching left edge into `skip`.
            have hOuterMem :
                TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
                    edge.symbol.offers ∈ signature.transitionAlphabet := by
              simpa [compileType] using hSymbolMem
            have hChildSymbol :
                TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
                    (TypeOfferSummary.mk edge.symbol.offers.current childFuture) ∈
                  (compileType signature left).alphabet := by
              change TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
                  (TypeOfferSummary.mk edge.symbol.offers.current childFuture) ∈
                signature.transitionAlphabet
              exact transitionAlphabet_of_typeOffers_target_subset signature
                hOuterMem hChildStep.2
                (by simp [typeFutureOffers, typeFutureOffersFuel])
            obtain ⟨q1', hChildEdge, hChildTargetRelated⟩ :=
              hLeftForward hMem hChildSymbol hChildStep
            have hParentSymbol :
                TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
                    (TypeOfferSummary.mk edge.symbol.offers.current
                      (typeFutureOffers right \ edge.symbol.offers.current)) ∈
                  signature.transitionAlphabet := by
              rw [← hFutureEq]; exact hOuterMem
            obtain ⟨hParentEdge, -⟩ :=
              compileType_seq_lift_left_fuse signature left right hParentSource hMem
                hChildTargetRelated hChildStep hParentSymbol hChildEdge
            have hOuterEdge :
                (compileType signature (.seq left right)).HasEdge entry.2
                  edge.symbol.environment edge.symbol.label edge.symbol.offers
                  successor.2 := by
              rw [← hSource, hTarget]; exact hEdgeMem
            have hSuccessorEq : successor.2 = .child 1
                (compileType signature right).initial := by
              apply compileType_hasEdge_target_unique signature (.seq left right)
                hOuterEdge
              rw [hEntry2, show edge.symbol.offers = TypeOfferSummary.mk
                edge.symbol.offers.current edge.symbol.offers.future from rfl, hFutureEq]
              exact hParentEdge
            exact Or.inr ⟨(compileType signature right).initial, hSuccessorEq,
              hTargetEq' ▸ buildRelationSet_initial right (compileType signature right)⟩
      · -- entry is a right state, representing its own relation's residual
        have hEntry2 : entry.2 = .child 1 q2 := by rw [hStateEq]
        have hChildSource : pendingEdge.source = .child 1 q2 := by
          rw [hPSource, hSource, hEntry2]
        obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
          (buildSequenceAutomaton_outgoing_right signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            q2 pendingEdge).mp ⟨hPendingMem, hChildSource⟩
        have hInnerEdgeMem : (compileType signature right).HasEdge q2
            edge.symbol.environment edge.symbol.label edge.symbol.offers
            childEdge.target := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature right q2
            childEdge.target edge.symbol.environment edge.symbol.label
            edge.symbol.offers hSymbolMem]
          refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
          · rw [← hPEnv, hChildEdgeEq]; rfl
          · rw [← hPLabel, hChildEdgeEq]; rfl
          · rw [← hPCurrent, hChildEdgeEq]; rfl
          · rw [← hPFuture, hChildEdgeEq]
            cases hSpec : childEdge.future with
            | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
            | «at» t r =>
                have hStateMem := compileTypeFuel_futureTargetsInStates signature
                  (typeCompilationFuel right) right le_rfl childEdge hChildEdgeMem t r
                  hSpec
                simp only [childPendingEdge, childFutureSpec, hSpec, childState]
                rw [computeFutureOf_sequence_right signature left right t hStateMem]
        have hTargetEq : successor.2 = .child 1 childEdge.target := by
          rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
        have hInnerMem :=
          relationMembership_of_step_edge_unique right (compileType signature right)
            hMem hInnerEdgeMem hStep
            (fun target hTargetStep =>
              decoratedTypeTransition_target_unique hTargetStep hStep)
        exact Or.inr ⟨childEdge.target, hTargetEq, hInnerMem⟩)
  exact (hResult (residual, state) hRelated).2

/-- Proves every public sequence edge leaving a related state belongs to one of the sequence edge families. -/
theorem compileType_seq_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftForward :
      ∀ {residual' : PactType} {q1 : TypeAutomatonState} {env : TypeEnvironment}
        {label : TypeLabel} {offers : TypeOfferSummary} {target : PactType},
        relationMembership (buildRelationSet left (compileType signature left))
          residual' q1 →
        (TypeAutomatonSymbol.mk env label offers ∈
          (compileType signature left).alphabet) →
        DecoratedTypeTransition env residual' label offers target →
        ∃ q1', (compileType signature left).HasEdge q1 env label offers q1' ∧
          relationMembership (buildRelationSet left (compileType signature left))
            target q1')
    {residual residual' : PactType}
    {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        residual state)
    (hEdge :
      (compileType signature (.seq left right)).HasEdge state env label
        (TypeOfferSummary.mk current future) state')
    (hTarget :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        residual' state') :
    SeqCompiledEdgeCase signature left right residual residual' state state'
      env label current future := by
  rcases relationMembership_seq_cases signature left right hLeftForward hRelated with
    hLeft | hRight
  · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated⟩
    cases hEntry
    exact helper_h15_sequence_left_public_edge_cases signature left right
      hRelated hLeftRelated hEdge hTarget
  · rcases hRight with ⟨q, hState, hRightRelated⟩
    simp only at hState hRightRelated
    subst state
    have hSymbol := compileType_hasEdge_symbol_mem signature (.seq left right)
      hEdge
    have hResolved :=
      (compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
        (.child 1 q) state' env label (TypeOfferSummary.mk current future)
        hSymbol).mp hEdge
    rw [compileTypeFuel_sequence_eq_build signature left right] at hResolved
    rcases hResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
      hPendingEnv, hPendingLabel, hPendingCurrent, hPendingFuture,
      hPendingTarget⟩
    obtain ⟨childEdge, hChildEdgeMem, hChildSource, hChildEdgeEq⟩ :=
      (buildSequenceAutomaton_outgoing_right signature
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        q pendingEdge).mp ⟨hPendingMem, hPendingSource⟩
    have hTargetState : state' = .child 1 childEdge.target := by
      rw [← hPendingTarget, hChildEdgeEq]
      rfl
    have hRightTargetRelated :
        relationMembership (buildRelationSet right (compileType signature right))
          residual' childEdge.target := by
      rcases relationMembership_seq_cases signature left right hLeftForward hTarget with
        hTargetLeft | hTargetRight
      · rcases hTargetLeft with ⟨qLeft, leftResidual, hEntry, _hLeftTarget⟩
        have hStateEq := congrArg Prod.snd hEntry
        exfalso
        rw [hTargetState] at hStateEq
        cases hStateEq
      · rcases hTargetRight with ⟨qTarget, hTargetEq, hRightTarget⟩
        have hQ : qTarget = childEdge.target := by
          rw [hTargetState] at hTargetEq
          cases hTargetEq
          rfl
        subst qTarget
        exact hRightTarget
    have hChildEdge :
        (compileType signature right).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
      rw [compileType_hasEdge_iff_hasResolvedEdge signature right q
        childEdge.target env label (TypeOfferSummary.mk current future)
        hSymbol]
      refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
      · rw [← hPendingEnv, hChildEdgeEq]
        rfl
      · rw [← hPendingLabel, hChildEdgeEq]
        rfl
      · rw [← hPendingCurrent, hChildEdgeEq]
        rfl
      · cases hSpec : childEdge.future with
        | explicit offers =>
            simpa [hChildEdgeEq, childPendingEdge, childFutureSpec, hSpec]
              using hPendingFuture
        | «at» futureTarget removed =>
            have hStateMem := compileTypeFuel_futureTargetsInStates signature
              (typeCompilationFuel right) right le_rfl childEdge hChildEdgeMem
              futureTarget removed hSpec
            have hSeqFuture :=
              computeFutureOf_sequence_right signature left right futureTarget
                hStateMem
            have hSeqFuture' :
                computeFutureOf signature (.seq left right)
                    (childState 1 futureTarget) =
                  computeFutureOf signature right futureTarget := by
              simpa [childState] using hSeqFuture
            simpa [hChildEdgeEq, childPendingEdge, childFutureSpec, hSpec,
              hSeqFuture'] using hPendingFuture
    exact SeqCompiledEdgeCase.rightStep q childEdge.target rfl hTargetState
      hRightRelated hRightTargetRelated hChildEdge

end

end Pact
