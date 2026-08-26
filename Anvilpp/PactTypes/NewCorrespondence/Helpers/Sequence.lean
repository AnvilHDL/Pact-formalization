import Anvilpp.PactTypes.NewCorrespondence.Helpers.ChoiceRelations

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def seqRelationShape
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 residualLeft,
      entry = (.seq alphabet residualLeft right, .child 0 q1) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1 ∧
      (q1 ∉ (compileType signature left).accepting ∨
        q1 = (compileType signature left).initial)) ∨
    (∃ q2, entry.2 = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        entry.1 q2)

/-- Lift a surviving left-child state into the left phase of a sequence. -/
lemma relationMembership_seq_left
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right residual : PactType)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet left (compileType signature left)) residual state)
    (hNotAccepting : state ∉ (compileType signature left).accepting) :
    relationMembership
      (buildRelationSet (.seq alphabet left right)
        (compileType signature (.seq alphabet left right)))
      (.seq alphabet residual right) (.child 0 state) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show ((.seq alphabet residual right : PactType), .child 0 state) ∈
    buildRelationSetCoreFuel signature
      (typeCompilationFuel (.seq alphabet left right))
      (.seq alphabet left right)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Prod.mk.injEq]
  left
  refine ⟨(residual, state), ⟨?_, ?_⟩, rfl, rfl⟩
  · rw [buildRelationSetCoreFuel_eq_of_sufficient signature left
      (le_max_left _ _) le_rfl]
    exact hRelated
  · have hCompile := compileTypeFuel_eq_of_sufficient signature left
      (le_max_left (typeCompilationFuel left) (typeCompilationFuel right)) le_rfl
    rw [hCompile]
    simp only [sequenceDeleted, Finset.mem_sdiff, Finset.mem_singleton]
    intro hAccepting
    exact (hNotAccepting (by simpa [compileType] using hAccepting.1)).elim

/-- Lift a right-child state into the right phase of a sequence. -/
lemma relationMembership_seq_right
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right residual : PactType)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet right (compileType signature right)) residual state) :
    relationMembership
      (buildRelationSet (.seq alphabet left right)
        (compileType signature (.seq alphabet left right)))
      residual (.child 1 state) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show (residual, .child 1 state) ∈
    buildRelationSetCoreFuel signature
      (typeCompilationFuel (.seq alphabet left right))
      (.seq alphabet left right)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image,
    Prod.mk.injEq]
  right
  refine ⟨(residual, state), ?_, rfl, rfl⟩
  rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
    (le_max_right _ _) le_rfl]
  exact hRelated

/-- Proves the sufficient-fuel sequence fragment is the sequence builder applied to the sufficient child fragments. -/
theorem compileTypeFuel_sequence_eq_build
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) :
    compileTypeFuel signature (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right) =
      buildSequenceAutomaton signature
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  rw [compileTypeFuel.eq_def]
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel right)
      right).states) :
    computeFutureOf signature (.seq alphabet left right) (.child 1 state) =
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
  have hSequenceFuel : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  obtain ⟨rightFuel, hRightFuel⟩ :
      ∃ fuel, typeCompilationFuel right = fuel + 1 := by
    have hPositive := typeCompilationFuel_positive right
    exact ⟨typeCompilationFuel right - 1, by omega⟩
  have hCompileSequence :
      compileTypeFuel signature
          (max (typeCompilationFuel left) (rightFuel + 1) + 1)
          (.seq alphabet left right) = sequence := by
    rw [← hRightFuel, ← hSequenceFuel]
    exact compileTypeFuel_sequence_eq_build signature alphabet left right
  have hCompileRight :
      compileTypeFuel signature (rightFuel + 1) right = rightFragment := by
    rw [← hRightFuel]
  unfold computeFutureOf
  rw [hSequenceFuel]
  conv_lhs => rw [computeFutureOfFuel]
  rw [hRightFuel]
  conv_rhs => rw [computeFutureOfFuel]
  rw [hCompileSequence, hCompileRight]
  change (parent.futureReachable (.child 1 state)).biUnion
      (_ : TypeAutomatonState → Finset BareMessage) =
    (child.futureReachable state).biUnion
      (_ : TypeAutomatonState → Finset BareMessage)
  rw [hReachable, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro visited _hVisited
  have hOffers := buildSequenceAutomaton_offersAt_right signature
    leftFragment rightFragment visited
  change parent.offersAt (.child 1 visited) = child.offersAt visited at hOffers
  rw [hOffers]
  have hInfo :
      stateProductInfo (.seq alphabet left right) (.child 1 visited) =
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
    (_hVisible : edge.label = .visible label)
    (hOutgoing :
      edge ∈ (buildSequenceAutomaton signature left right).edges ∧
        edge.source = .child 0 state) :
    ∃ childEdge ∈ left.edges,
      childEdge.source = state ∧ edge = sequenceLeftEdge left right childEdge := by
  classical
  rcases hOutgoing with ⟨hEdge, hSource⟩
  simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceLeftEdges,
    sequenceRightEdges, sequenceRedirectEdges, childPendingEdges,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with (hLeft | hRight) | hRedirect
  · rcases hLeft with ⟨childEdge, ⟨hChildMem, hNotAccepting⟩, hEdgeEq⟩
    have hChildSource := hSource
    rw [← hEdgeEq] at hChildSource
    simp [sequenceKeptLeftEdge, childState] at hChildSource
    exact ⟨childEdge, hChildMem, hChildSource,
      by rw [← hEdgeEq, sequenceLeftEdge, if_neg hNotAccepting]⟩
  · rcases hRight with ⟨childEdge, _, hEdgeEq⟩
    rw [← hEdgeEq] at hSource
    simp [childPendingEdge, childState] at hSource
  · rcases hRedirect with ⟨childEdge, ⟨hChildMem, hAccepting⟩, hEdgeEq⟩
    have hChildSource := hSource
    rw [← hEdgeEq] at hChildSource
    simp [sequenceRedirectEdge, childState] at hChildSource
    exact ⟨childEdge, hChildMem, hChildSource,
      by rw [← hEdgeEq, sequenceLeftEdge, if_pos hAccepting]⟩

/-- Proves H15's future agreement for a retained left target of a sequence step. -/
lemma helper_h15_sequence_left_step_future_offers_agree
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {leftTarget : PactType} {q' : TypeAutomatonState}
    (hTarget :
      relationMembership (buildRelationSet left (compileType signature left))
        leftTarget q')
    (hNonFinal : leftTarget ≠ .skip leftTarget.alphabet) :
    computeFutureOf signature (.seq alphabet left right) (.child 0 q') =
      typeFutureOffers (.seq alphabet leftTarget right) := by
  sorry

/-- Proves H15's future agreement for the right entry reached by a fused sequence step. -/
lemma helper_h15_sequence_left_fuse_future_offers_agree
    (signature : TypeAlphabet) (alphabet skipAlphabet : PactTypeAlphabet)
    (left right : PactType)
    {q' : TypeAutomatonState}
    (_hTarget :
      relationMembership (buildRelationSet left (compileType signature left))
        (.skip skipAlphabet) q') :
    computeFutureOf signature (.seq alphabet left right)
        (.child 1 (compileType signature right).initial) =
      typeFutureOffers right := by
  rw [computeFutureOf_sequence_right signature alphabet left right
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {rightTarget : PactType} {q' : TypeAutomatonState}
    (hTarget :
      relationMembership (buildRelationSet right (compileType signature right))
        rightTarget q') :
    computeFutureOf signature (.seq alphabet left right) (.child 1 q') =
      typeFutureOffers rightTarget := by
  sorry

/-- Describes the two semantic forms of a decorated sequence step. -/
inductive SeqDecoratedStepCase
    (alphabet : PactTypeAlphabet) (right : PactType)
    (source target : PactType)
    (env : TypeEnvironment) (label : TypeLabel)
    (current future : Finset BareMessage) : Prop where
  | step (leftTarget : PactType) (childFuture : Finset BareMessage) :
      target = .seq alphabet leftTarget right →
      leftTarget ≠ .skip leftTarget.alphabet →
      DecoratedTypeTransition env source label
        (TypeOfferSummary.mk current childFuture) leftTarget →
      future = typeFutureOffers (.seq alphabet leftTarget right) \ current →
      SeqDecoratedStepCase alphabet right source target env label current future
  | fuse (transitionSkipAlphabet offerSkipAlphabet : PactTypeAlphabet)
      (childFuture : Finset BareMessage) :
      target = right →
      TypeTransition env source label (.skip transitionSkipAlphabet) →
      TypeOffers env source label (.skip offerSkipAlphabet) current childFuture →
      future = typeFutureOffers right \ current →
      SeqDecoratedStepCase alphabet right source target env label current future

/-- Proves that every decorated sequence step is either retained on the left or fused into the right operand. -/
theorem decoratedTypeTransition_seq_cases
    {env : TypeEnvironment} {label : TypeLabel}
    {alphabet : PactTypeAlphabet} {left right target : PactType}
    {current future : Finset BareMessage}
    (hStep :
      DecoratedTypeTransition env (.seq alphabet left right) label
        (TypeOfferSummary.mk current future) target) :
    SeqDecoratedStepCase alphabet right left target env label current future := by
  rcases hStep with ⟨hTransition, hOffers⟩
  cases hTransition with
  | seq_fuse env alphabet transitionSkipAlphabet left right label
      hChildTransition =>
      have hOfferCase : ∃ offerSkipAlphabet childFuture,
          TypeOffers env left label (.skip offerSkipAlphabet) current
              childFuture ∧
            future = typeFutureOffers right \ current := by
        change TypeOffers env (.seq alphabet left right) label right current
          future at hOffers
        cases hOffers
        exact ⟨_, _, by assumption, rfl⟩
      obtain ⟨offerSkipAlphabet, childFuture, hChildOffers, hFuture⟩ :=
        hOfferCase
      exact SeqDecoratedStepCase.fuse transitionSkipAlphabet offerSkipAlphabet
        childFuture rfl hChildTransition hChildOffers hFuture
  | seq env alphabet left leftTarget right label hChildTransition hNonFinal =>
      have hChildOffers :
          ∃ childFuture,
            TypeOffers env left label leftTarget current childFuture ∧
              future = typeFutureOffers (.seq alphabet leftTarget right) \
                current := by
        change TypeOffers env (.seq alphabet left right) label
          (.seq alphabet leftTarget right) current future at hOffers
        cases hOffers
        aesop
      rcases hChildOffers with ⟨childFuture, hChildOffers, hFuture⟩
      exact SeqDecoratedStepCase.step leftTarget childFuture rfl hNonFinal
        ⟨hChildTransition, hChildOffers⟩ hFuture

/-- Describes the public edge families leaving a related compiled sequence state. -/
inductive SeqCompiledEdgeCase
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (residual residual' : PactType)
    (state state' : TypeAutomatonState)
    (env : TypeEnvironment) (label : TypeLabel)
    (current future : Finset BareMessage) : Prop where
  | leftStep (leftResidual leftTarget : PactType)
      (q q' : TypeAutomatonState) (childFuture : Finset BareMessage) :
      residual = .seq alphabet leftResidual right →
      residual' = .seq alphabet leftTarget right →
      state = .child 0 q →
      state' = .child 0 q' →
      leftTarget ≠ .skip leftTarget.alphabet →
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q →
      relationMembership (buildRelationSet left (compileType signature left))
        leftTarget q' →
      (compileType signature left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q' →
      future = typeFutureOffers (.seq alphabet leftTarget right) \ current →
      SeqCompiledEdgeCase signature alphabet left right residual residual' state state'
        env label current future
  | leftFuse (leftResidual : PactType)
      (skipAlphabet : PactTypeAlphabet) (q q' : TypeAutomatonState)
      (childFuture : Finset BareMessage) :
      residual = .seq alphabet leftResidual right →
      residual' = right →
      state = .child 0 q →
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q →
      relationMembership (buildRelationSet left (compileType signature left))
        (.skip skipAlphabet) q' →
      (compileType signature left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q' →
      future = typeFutureOffers right \ current →
      SeqCompiledEdgeCase signature alphabet left right residual residual' state state'
        env label current future
  | entryFuse (skipAlphabet : PactTypeAlphabet) :
      residual = .seq alphabet (.skip skipAlphabet) right →
      residual' = right →
      state = .child 0 (compileType signature left).initial →
      state' = .child 1 (compileType signature right).initial →
      label = TypeLabel.silent →
      current = ∅ →
      future = typeFutureOffers right →
      env.WellFormed →
      env.clock = false →
      SeqCompiledEdgeCase signature alphabet left right residual residual' state state'
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
      SeqCompiledEdgeCase signature alphabet left right residual residual' state state'
        env label current future

/-- Proves a public edge from the left side of a sequence is retained or fused according to the child target. -/
lemma helper_h15_sequence_left_public_edge_cases
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {leftResidual residual' : PactType}
    {q state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        (.seq alphabet leftResidual right) (.child 0 q))
    (hLeftSource :
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q)
    (hEdge :
      (compileType signature (.seq alphabet left right)).HasEdge
        (.child 0 q) env label
        (TypeOfferSummary.mk current future) state')
    (hTarget :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        residual' state') :
    SeqCompiledEdgeCase signature alphabet left right
      (.seq alphabet leftResidual right) residual'
      (.child 0 q) state' env label current future := by
  have hFutureEq :
      future = typeFutureOffers residual' \ current :=
    helper_h15_edge_future_offers_agree signature hParentSource hTarget hEdge
  sorry

/-- Lifts a non-final left-child edge to a retained public sequence edge. -/
theorem compileType_seq_lift_left_step
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {leftResidual leftTarget : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current childFuture : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        (.seq alphabet leftResidual right) (.child 0 q))
    (_hSource :
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q)
    (hTarget :
      relationMembership (buildRelationSet left (compileType signature left))
        leftTarget q')
    (hNonFinal : leftTarget ≠ .skip leftTarget.alphabet)
    (hChildStep :
      DecoratedTypeTransition env leftResidual label
        (TypeOfferSummary.mk current childFuture) leftTarget)
    (hParentSymbol :
      TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq alphabet leftTarget right) \ current)) ∈
        signature.transitionAlphabet)
    (hChildEdge :
      (compileType signature left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q') :
    (compileType signature (.seq alphabet left right)).HasEdge
        (.child 0 q) env label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq alphabet leftTarget right) \ current))
        (.child 0 q') ∧
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        (.seq alphabet leftTarget right) (.child 0 q') := by
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
    helper_h15_sequence_left_step_future_offers_agree signature alphabet left right
      hTarget hNonFinal
  have hParentEdge :
      (compileType signature (.seq alphabet left right)).HasEdge
        (.child 0 q) env label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq alphabet leftTarget right) \ current))
        (.child 0 q') := by
    rw [compileType_hasEdge_iff_hasResolvedEdge signature
      (.seq alphabet left right)
      (.child 0 q) (.child 0 q') env label
      (TypeOfferSummary.mk current
        (typeFutureOffers (.seq alphabet leftTarget right) \ current))
      hParentSymbol]
    rw [compileTypeFuel_sequence_eq_build signature alphabet left right]
    have hNotAcceptingPending :
        pendingEdge.target ∉
          (compileTypeFuel signature (typeCompilationFuel left) left).accepting := by
      rw [hPendingTarget]; exact hNotAccepting
    refine ⟨sequenceKeptLeftEdge
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
      pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceLeftEdges,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      exact Or.inl (Or.inl ⟨pendingEdge, ⟨hPendingMem, hNotAcceptingPending⟩, rfl⟩)
    · simp [sequenceKeptLeftEdge, childState, hPendingSource]
    · simp [sequenceKeptLeftEdge, hPendingEnv]
    · simp [sequenceKeptLeftEdge, hPendingLabel]
    · simp [sequenceKeptLeftEdge, hPendingCurrent]
    · have hSeqFuture' :
          computeFutureOf signature (.seq alphabet left right)
              (childState 0 q') =
            typeFutureOffers (.seq alphabet leftTarget right) := by
        simpa [childState] using hSeqFuture
      simp [sequenceKeptLeftEdge, hPendingCurrent, hPendingTarget,
        sequenceRedirect_of_not_accepting hNotAccepting, hSeqFuture']
    · simp [sequenceKeptLeftEdge, childState, hPendingTarget]
  have hParentStep :
      DecoratedTypeTransition env (.seq alphabet leftResidual right) label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq alphabet leftTarget right) \ current))
        (.seq alphabet leftTarget right) :=
    ⟨TypeTransition.seq env alphabet leftResidual leftTarget right label hChildStep.1
        hNonFinal,
      TypeOffers.seq env alphabet leftResidual leftTarget right label current
        childFuture hChildStep.2 hNonFinal⟩
  refine ⟨hParentEdge, ?_⟩
  exact relationMembership_seq_left signature alphabet left right leftTarget hTarget
    hNotAccepting

/-- Lifts a final left-child edge to the redirected public sequence edge. -/
theorem compileType_seq_lift_left_fuse
    (signature : TypeAlphabet) (alphabet skipAlphabet : PactTypeAlphabet)
    (left right : PactType)
    {leftResidual : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current childFuture : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        (.seq alphabet leftResidual right) (.child 0 q))
    (_hSource :
      relationMembership (buildRelationSet left (compileType signature left))
        leftResidual q)
    (hTarget :
      relationMembership (buildRelationSet left (compileType signature left))
        (.skip skipAlphabet) q')
    (hChildStep :
      DecoratedTypeTransition env leftResidual label
        (TypeOfferSummary.mk current childFuture) (.skip skipAlphabet))
    (hParentSymbol :
      TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current)) ∈
        signature.transitionAlphabet)
    (hChildEdge :
      (compileType signature left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q') :
    (compileType signature (.seq alphabet left right)).HasEdge
      (.child 0 q) env label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current))
        (.child 1 (compileType signature right).initial) ∧
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
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
    helper_h15_sequence_left_fuse_future_offers_agree signature alphabet
      skipAlphabet left right hTarget
  have hParentEdge :
      (compileType signature (.seq alphabet left right)).HasEdge
        (.child 0 q) env label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current))
        (.child 1 (compileType signature right).initial) := by
    rw [compileType_hasEdge_iff_hasResolvedEdge signature
      (.seq alphabet left right)
      (.child 0 q) (.child 1 (compileType signature right).initial) env label
      (TypeOfferSummary.mk current (typeFutureOffers right \ current))
      hParentSymbol]
    rw [compileTypeFuel_sequence_eq_build signature alphabet left right]
    refine ⟨sequenceRedirectEdge
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
      pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceRedirectEdges,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      exact Or.inr ⟨pendingEdge, ⟨hPendingMem, hPendingTarget ▸ hAccepting⟩, rfl⟩
    · simp [sequenceRedirectEdge, childState, hPendingSource]
    · simp [sequenceRedirectEdge, hPendingEnv]
    · simp [sequenceRedirectEdge, hPendingLabel]
    · simp [sequenceRedirectEdge, hPendingCurrent]
    · have hSeqFuture' :
          computeFutureOf signature (.seq alphabet left right)
              (childState 1
                (compileTypeFuel signature (typeCompilationFuel right) right).initial) =
            typeFutureOffers right := by
        simpa [compileType, childState] using hSeqFuture
      simp [sequenceRedirectEdge, hPendingCurrent, hSeqFuture']
    · simp [sequenceRedirectEdge, compileType, childState]
  have hParentStep :
      DecoratedTypeTransition env (.seq alphabet leftResidual right) label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current))
        right :=
    ⟨TypeTransition.seq_fuse env alphabet skipAlphabet leftResidual right label
        hChildStep.1,
      TypeOffers.seq_fuse env alphabet skipAlphabet leftResidual right label
        current childFuture hChildStep.2⟩
  refine ⟨hParentEdge, ?_⟩
  exact relationMembership_seq_right signature alphabet left right right
    (buildRelationSet_initial right (compileType signature right))

/-- Lifts a right-child edge to a copied public sequence edge. -/
theorem compileType_seq_lift_right_step
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {rightResidual rightTarget : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
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
      (compileType signature (.seq alphabet left right)).HasEdge
        (.child 1 q) env label
        offers state' ∧
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        rightTarget state' := by
  have hChildSymbol := compileType_hasEdge_symbol_mem signature right hChildEdge
  have hChildResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature right q q' env label
      offers hChildSymbol).mp hChildEdge
  rcases hChildResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, hPendingFuture,
    hPendingTarget⟩
  have hParentEdge :
      (compileType signature (.seq alphabet left right)).HasEdge
        (.child 1 q) env label
        offers (.child 1 q') := by
    rw [compileType_hasEdge_iff_hasResolvedEdge signature
      (.seq alphabet left right)
      (.child 1 q) (.child 1 q') env label offers hChildSymbol]
    rw [compileTypeFuel_sequence_eq_build signature alphabet left right]
    refine ⟨childPendingEdge 1 pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceRightEdges,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨pendingEdge, hPendingMem, rfl⟩)
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
            computeFutureOf_sequence_right signature alphabet left right futureTarget
              hStateMem
          have hSeqFuture' :
              computeFutureOf signature (.seq alphabet left right)
                  (childState 1 futureTarget) =
                computeFutureOf signature right futureTarget := by
            simpa [childState] using hSeqFuture
          simpa [childPendingEdge, childFutureSpec, hSpec, hSeqFuture'] using
            hPendingFuture
    · simp [childPendingEdge, childState, hPendingTarget]
  refine ⟨.child 1 q', hParentEdge, ?_⟩
  exact relationMembership_seq_right signature alphabet left right rightTarget
    _hTarget

/-- Proves every related sequence pair has the sequence shape, given the forward direction of the left child's own step correspondence. -/
lemma relationMembership_seq_cases
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        residual state) :
    seqRelationShape signature alphabet left right (residual, state) := by
  rcases helper_h12_seq_shape signature alphabet left right hRelated with
    hLeft | hRight
  · rcases hLeft with ⟨residualLeft, q1, hResidual, hState,
      hLeftRelated, hSurvives⟩
    exact Or.inl ⟨q1, residualLeft, by simp [hResidual, hState],
      hLeftRelated, hSurvives⟩
  · rcases hRight with ⟨q2, hState, hRightRelated⟩
    exact Or.inr ⟨q2, by simpa using hState, hRightRelated⟩

/-- Proves every public sequence edge leaving a related state belongs to one of the sequence edge families. -/
theorem compileType_seq_edge_cases
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {residual residual' : PactType}
    {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        residual state)
    (hEdge :
      (compileType signature (.seq alphabet left right)).HasEdge state env label
        (TypeOfferSummary.mk current future) state')
    (hTarget :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        residual' state') :
    SeqCompiledEdgeCase signature alphabet left right residual residual' state state'
      env label current future := by
  rcases relationMembership_seq_cases signature alphabet left right hRelated with
    hLeft | hRight
  · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _hSurvives⟩
    cases hEntry
    exact helper_h15_sequence_left_public_edge_cases signature alphabet left right
      hRelated hLeftRelated hEdge hTarget
  · rcases hRight with ⟨q, hState, hRightRelated⟩
    simp only at hState hRightRelated
    subst state
    have hSymbol := compileType_hasEdge_symbol_mem signature
      (.seq alphabet left right)
      hEdge
    have hResolved :=
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.seq alphabet left right)
        (.child 1 q) state' env label (TypeOfferSummary.mk current future)
        hSymbol).mp hEdge
    rw [compileTypeFuel_sequence_eq_build signature alphabet left right]
      at hResolved
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
      rcases relationMembership_seq_cases signature alphabet left right hTarget with
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
              computeFutureOf_sequence_right signature alphabet left right
                futureTarget
                hStateMem
            have hSeqFuture' :
                computeFutureOf signature (.seq alphabet left right)
                    (childState 1 futureTarget) =
                  computeFutureOf signature right futureTarget := by
              simpa [childState] using hSeqFuture
            simpa [hChildEdgeEq, childPendingEdge, childFutureSpec, hSpec,
              hSeqFuture'] using hPendingFuture
    exact SeqCompiledEdgeCase.rightStep q childEdge.target rfl hTargetState
      hRightRelated hRightTargetRelated hChildEdge

end

end Pact
