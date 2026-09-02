import Anvilpp.PactTypes.NewCorrespondence.Helpers.ChoiceRelations

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def seqRelationShape
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 residualLeft,
      entry = (.seq alphabet residualLeft right, .child 0 q1) ∧
      relationMembership (buildRelationSet left (compileType left))
        residualLeft q1 ∧
      (q1 ∉ (compileType left).accepting ∨
        q1 = (compileType left).initial)) ∨
    (∃ q2, entry.2 = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType right))
        entry.1 q2)

/-- Lift a surviving left-child state into the left phase of a sequence. -/
lemma relationMembership_seq_left
     (alphabet : PactTypeAlphabet)
    (left right residual : PactType)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet left (compileType left)) residual state)
    (hNotAccepting : state ∉ (compileType left).accepting) :
    relationMembership
      (buildRelationSet (.seq alphabet left right)
        (compileType (.seq alphabet left right)))
      (.seq alphabet residual right) (.child 0 state) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show ((.seq alphabet residual right : PactType), .child 0 state) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.seq alphabet left right))
      (.seq alphabet left right)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Prod.mk.injEq]
  left
  refine ⟨(residual, state), ⟨?_, ?_⟩, rfl, rfl⟩
  · rw [buildRelationSetCoreFuel_eq_of_sufficient left
      (le_max_left _ _) le_rfl]
    exact hRelated
  · have hCompile := compileTypeFuel_eq_of_sufficient left
      (le_max_left (typeCompilationFuel left) (typeCompilationFuel right)) le_rfl
    rw [hCompile]
    simp only [sequenceDeleted, Finset.mem_sdiff, Finset.mem_singleton]
    intro hAccepting
    exact (hNotAccepting (by simpa [compileType] using hAccepting.1)).elim

/-- Lift a right-child state into the right phase of a sequence. -/
lemma relationMembership_seq_right
     (alphabet : PactTypeAlphabet)
    (left right residual : PactType)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet right (compileType right)) residual state) :
    relationMembership
      (buildRelationSet (.seq alphabet left right)
        (compileType (.seq alphabet left right)))
      residual (.child 1 state) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show (residual, .child 1 state) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.seq alphabet left right))
      (.seq alphabet left right)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image,
    Prod.mk.injEq]
  right
  refine ⟨(residual, state), ?_, rfl, rfl⟩
  rw [buildRelationSetCoreFuel_eq_of_sufficient right
    (le_max_right _ _) le_rfl]
  exact hRelated

/-- Proves the sufficient-fuel sequence fragment is the sequence builder applied to the sufficient child fragments. -/
theorem compileTypeFuel_sequence_eq_build
     (alphabet : PactTypeAlphabet)
    (left right : PactType) :
    compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right) =
      buildSequenceAutomaton
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  rw [compileTypeFuel.eq_def]
  show buildSequenceAutomaton
      (compileTypeFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compileTypeFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right) =
    buildSequenceAutomaton
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
  rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
    compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]

private theorem buildSequenceAutomaton_referencedStates_right
     (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton left right
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
      (buildSequenceAutomaton_outgoing_right left right state edge).mp
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
    · exact (buildSequenceAutomaton_outgoing_right left right state
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
     (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton left right
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
      (buildSequenceAutomaton_outgoing_right left right state edge).mp
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
    · exact (buildSequenceAutomaton_outgoing_right left right state
        (childPendingEdge 1 childEdge)).mpr
          ⟨childEdge, hChildEdgeMem, hChildSource, rfl⟩
    · cases hFuture : childEdge.future <;>
        simpa [childPendingEdge, childFutureSpec, childState, hFuture] using hOffer

/-- Proves a `.child 1`-tagged state's future menu, in a compiled sequence, agrees with the right child's own. -/
theorem computeFutureOf_sequence_right
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hDisjoint : right.OfferBranchesDisjoint)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel (typeCompilationFuel right)
      right).states) :
    computeFutureOf (.seq alphabet left right) (.child 1 state) =
      computeFutureOf right state := by
  classical
  let leftFragment :=
    compileTypeFuel (typeCompilationFuel left) left
  let rightFragment :=
    compileTypeFuel (typeCompilationFuel right) right
  let sequence := buildSequenceAutomaton leftFragment rightFragment
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
    · exact buildSequenceAutomaton_referencedStates_right
        leftFragment rightFragment
    · exact compileTypeFuel_referencesClosed
        (typeCompilationFuel right) right le_rfl hDisjoint
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
      compileTypeFuel
          (max (typeCompilationFuel left) (rightFuel + 1) + 1)
          (.seq alphabet left right) = sequence := by
    rw [← hRightFuel, ← hSequenceFuel]
    exact compileTypeFuel_sequence_eq_build alphabet left right
  have hCompileRight :
      compileTypeFuel (rightFuel + 1) right = rightFragment := by
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
  have hOffers := buildSequenceAutomaton_offersAt_right
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
      rw [computeFutureOfFuel_eq_of_sufficient productLeft q1
          hLeftLarge hLeftSmall,
        computeFutureOfFuel_eq_of_sufficient productRight q2
          hRightLarge hRightSmall]

/-- Proves visible sequence edges leaving a left-child state are either rewritten left edges or the entry bridge. -/
theorem buildSequenceAutomaton_outgoing_left_visible
     (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge)
    {label : TypeLabel}
    (_hVisible : edge.label = .visible label)
    (hOutgoing :
      edge ∈ (buildSequenceAutomaton left right).edges ∧
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
      by rw [← hEdgeEq, sequenceLeftEdge, if_neg hNotAccepting.2]⟩
  · rcases hRight with ⟨childEdge, _, hEdgeEq⟩
    rw [← hEdgeEq] at hSource
    simp [childPendingEdge, childState] at hSource
  · rcases hRedirect with ⟨childEdge, ⟨hChildMem, hAccepting⟩, hEdgeEq⟩
    have hChildSource := hSource
    rw [← hEdgeEq] at hChildSource
    simp [sequenceRedirectEdge, childState] at hChildSource
    exact ⟨childEdge, hChildMem, hChildSource,
      by rw [← hEdgeEq, sequenceLeftEdge, if_pos hAccepting.2]⟩

/-- Proves H15's future agreement for a retained left target of a sequence step. -/
lemma helper_h15_sequence_left_step_future_offers_agree
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {leftTarget : PactType} {q' : TypeAutomatonState}
    (hTarget :
      relationMembership (buildRelationSet left (compileType left))
        leftTarget q')
    (hNonFinal : leftTarget ≠ .skip leftTarget.alphabet) :
    computeFutureOf (.seq alphabet left right) (.child 0 q') =
      typeFutureOffers (.seq alphabet leftTarget right) := by
  have hNotAccepting :
      q' ∉ (compileType left).accepting := by
    intro hAccepting
    exact hNonFinal
      ((helper_h13_final_states_represent_completion hTarget).mp
        hAccepting)
  exact helper_h15_future_offers_agree
    (relationMembership_seq_left alphabet left right leftTarget
      hTarget hNotAccepting)

/-- Proves H15's future agreement for the right entry reached by a fused sequence step. -/
lemma helper_h15_sequence_left_fuse_future_offers_agree
     (alphabet skipAlphabet : PactTypeAlphabet)
    (left right : PactType)
    (hDisjoint : right.OfferBranchesDisjoint)
    {q' : TypeAutomatonState}
    (_hTarget :
      relationMembership (buildRelationSet left (compileType left))
        (.skip skipAlphabet) q') :
    computeFutureOf (.seq alphabet left right)
        (.child 1 (compileType right).initial) =
      typeFutureOffers right := by
  rw [computeFutureOf_sequence_right alphabet left right hDisjoint
    (compileType right).initial
    (by
      show (compileTypeFuel (typeCompilationFuel right) right).initial ∈
        (compileTypeFuel (typeCompilationFuel right) right).states
      exact compileTypeFuel_initial_mem (typeCompilationFuel right)
        right le_rfl)]
  exact helper_h15_future_offers_agree
    (buildRelationSet_initial right (compileType right))

/-- Proves H15's future agreement for a right-child target of a sequence step. -/
lemma helper_h15_sequence_right_future_offers_agree
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {rightTarget : PactType} {q' : TypeAutomatonState}
    (hTarget :
      relationMembership (buildRelationSet right (compileType right))
        rightTarget q') :
    computeFutureOf (.seq alphabet left right) (.child 1 q') =
      typeFutureOffers rightTarget := by
  exact helper_h15_future_offers_agree
    (relationMembership_seq_right alphabet left right rightTarget
      hTarget)

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
      label ≠ TypeLabel.tock →
      future = typeFutureOffers (.seq alphabet leftTarget right) \ current →
      SeqDecoratedStepCase alphabet right source target env label current future
  | stepTock (leftTarget : PactType)
      (childCurrent childFuture : Finset BareMessage) :
      target = .seq alphabet leftTarget right →
      leftTarget ≠ .skip leftTarget.alphabet →
      label = TypeLabel.tock →
      DecoratedTypeTransition env source label
        (TypeOfferSummary.mk childCurrent childFuture) leftTarget →
      future = ∅ →
      SeqDecoratedStepCase alphabet right source target env label current future
  | fuse (transitionSkipAlphabet offerSkipAlphabet : PactTypeAlphabet)
      (childFuture : Finset BareMessage) :
      target = right →
      TypeTransition env source label (.skip transitionSkipAlphabet) →
      TypeOffers env source label (.skip offerSkipAlphabet) current childFuture →
      label ≠ TypeLabel.tock →
      future = typeFutureOffers right \ current →
      SeqDecoratedStepCase alphabet right source target env label current future
  | fuse_tock (transitionSkipAlphabet offerSkipAlphabet : PactTypeAlphabet)
      (childCurrent childFuture : Finset BareMessage) :
      target = right →
      label = TypeLabel.tock →
      TypeTransition env source label (.skip transitionSkipAlphabet) →
      TypeOffers env source label (.skip offerSkipAlphabet)
        childCurrent childFuture →
      future = ∅ →
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
      change TypeOffers env (.seq alphabet left right) label right current
        future at hOffers
      cases hOffers with
      | seq_fuse _ _ offerSkipAlphabet _ _ _ _ childFuture hChildOffers hNotTock =>
          exact SeqDecoratedStepCase.fuse transitionSkipAlphabet
            offerSkipAlphabet childFuture rfl hChildTransition hChildOffers
            hNotTock rfl
      | seq_fuse_tock _ _ offerSkipAlphabet _ _ childCurrent childFuture
          hChildOffers =>
          exact SeqDecoratedStepCase.fuse_tock transitionSkipAlphabet
            offerSkipAlphabet childCurrent childFuture rfl rfl hChildTransition
            hChildOffers rfl
  | seq env alphabet left leftTarget right label hChildTransition hNonFinal =>
      change TypeOffers env (.seq alphabet left right) label
        (.seq alphabet leftTarget right) current future at hOffers
      cases hOffers with
      | seq _ _ _ _ _ _ _ childFuture hChildOffers _ hNotTock =>
          exact SeqDecoratedStepCase.step leftTarget childFuture rfl hNonFinal
            ⟨hChildTransition, hChildOffers⟩ hNotTock rfl
      | seq_tock _ _ _ _ _ childCurrent childFuture hChildOffers _ =>
          exact SeqDecoratedStepCase.stepTock leftTarget childCurrent
            childFuture rfl hNonFinal rfl
            ⟨hChildTransition, hChildOffers⟩ rfl

/-- Describes the public edge families leaving a related compiled sequence state. -/
inductive SeqCompiledEdgeCase
     (alphabet : PactTypeAlphabet)
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
      relationMembership (buildRelationSet left (compileType left))
        leftResidual q →
      relationMembership (buildRelationSet left (compileType left))
        leftTarget q' →
      (compileType left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q' →
      label ≠ TypeLabel.tock →
      future = typeFutureOffers (.seq alphabet leftTarget right) \ current →
      SeqCompiledEdgeCase alphabet left right residual residual' state state'
        env label current future
  | leftStepTock (leftResidual leftTarget : PactType)
      (q q' : TypeAutomatonState) (childFuture : Finset BareMessage) :
      residual = .seq alphabet leftResidual right →
      residual' = .seq alphabet leftTarget right →
      state = .child 0 q →
      state' = .child 0 q' →
      leftTarget ≠ .skip leftTarget.alphabet →
      relationMembership (buildRelationSet left (compileType left))
        leftResidual q →
      relationMembership (buildRelationSet left (compileType left))
        leftTarget q' →
      (compileType left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q' →
      label = TypeLabel.tock →
      future = ∅ →
      SeqCompiledEdgeCase alphabet left right residual residual' state state'
        env label current future
  | leftFuse (leftResidual : PactType)
      (skipAlphabet : PactTypeAlphabet) (q q' : TypeAutomatonState)
      (childFuture : Finset BareMessage) :
      residual = .seq alphabet leftResidual right →
      residual' = right →
      state = .child 0 q →
      relationMembership (buildRelationSet left (compileType left))
        leftResidual q →
      relationMembership (buildRelationSet left (compileType left))
        (.skip skipAlphabet) q' →
      (compileType left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q' →
      label ≠ TypeLabel.tock →
      future = typeFutureOffers right \ current →
      SeqCompiledEdgeCase alphabet left right residual residual' state state'
        env label current future
  | leftFuseTock (leftResidual : PactType)
      (skipAlphabet : PactTypeAlphabet) (q q' : TypeAutomatonState)
      (childFuture : Finset BareMessage) :
      residual = .seq alphabet leftResidual right →
      residual' = right →
      state = .child 0 q →
      relationMembership (buildRelationSet left (compileType left))
        leftResidual q →
      relationMembership (buildRelationSet left (compileType left))
        (.skip skipAlphabet) q' →
      (compileType left).HasEdge q env TypeLabel.tock
        (TypeOfferSummary.mk current childFuture) q' →
      label = TypeLabel.tock →
      future = ∅ →
      SeqCompiledEdgeCase alphabet left right residual residual' state state'
        env label current future
  | rightStep (q q' : TypeAutomatonState) :
      state = .child 1 q →
      state' = .child 1 q' →
      relationMembership (buildRelationSet right (compileType right))
        residual q →
      relationMembership (buildRelationSet right (compileType right))
        residual' q' →
      (compileType right).HasEdge q env label
        (TypeOfferSummary.mk current future) q' →
      SeqCompiledEdgeCase alphabet left right residual residual' state state'
        env label current future

/-- Proves a public edge from the left side of a sequence is retained or fused according to the child target. -/
lemma helper_h15_sequence_left_public_edge_cases
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {leftResidual residual' : PactType}
    {q state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        (.seq alphabet leftResidual right) (.child 0 q))
    (hLeftSource :
      relationMembership (buildRelationSet left (compileType left))
        leftResidual q)
    (hEdge :
      (compileType (.seq alphabet left right)).HasEdge
        (.child 0 q) env label
        (TypeOfferSummary.mk current future) state')
    (hTarget :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        residual' state') :
    SeqCompiledEdgeCase alphabet left right
      (.seq alphabet leftResidual right) residual'
      (.child 0 q) state' env label current future := by
  have hFutureEq :
      future = if label = TypeLabel.tock then ∅
        else typeFutureOffers residual' \ current :=
    helper_h15_edge_future_offers_agree hParentSource hTarget hEdge
  classical
  let leftFragment :=
    compileTypeFuel (typeCompilationFuel left) left
  let rightFragment :=
    compileTypeFuel (typeCompilationFuel right) right
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge
      (.seq alphabet left right) (.child 0 q) state' env label
      (TypeOfferSummary.mk current future)).mp hEdge
  rw [compileTypeFuel_sequence_eq_build alphabet left right]
    at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, hPendingFuture,
    hPendingTarget⟩
  obtain ⟨childEdge, hChildEdgeMem, hChildSource, hChildEdgeEq⟩ :=
    buildSequenceAutomaton_outgoing_left_visible leftFragment
      rightFragment q pendingEdge hPendingLabel ⟨hPendingMem, hPendingSource⟩
  have hChildEnv : childEdge.environment = env := by
    have h := hPendingEnv
    rw [hChildEdgeEq] at h
    simpa [leftFragment, rightFragment] using h
  have hChildLabel : childEdge.label = .visible label := by
    have h := hPendingLabel
    rw [hChildEdgeEq] at h
    simpa [leftFragment, rightFragment] using h
  have hChildCurrent : childEdge.current = current := by
    have h := hPendingCurrent
    rw [hChildEdgeEq] at h
    simpa [leftFragment, rightFragment] using h
  obtain ⟨childTargetResidual, hChildTargetRelated⟩ :
      ∃ childTargetResidual,
        relationMembership (buildRelationSet left (compileType left))
          childTargetResidual childEdge.target := by
    have hTargetRaw :=
      buildRelationSetCoreFuel_edge_target_mem
        (typeCompilationFuel left) left le_rfl childEdge hChildEdgeMem
    rcases hTargetRaw with hTargetRaw | hMarker
    · rcases hTargetRaw with ⟨childTargetResidual, hTargetRaw⟩
      exact ⟨childTargetResidual, hTargetRaw⟩
    · rcases hMarker with ⟨markerName, hMarkerLabel⟩
      rw [hChildLabel] at hMarkerLabel
      cases hMarkerLabel
  let childFuture : Finset BareMessage :=
    match childEdge.future with
    | .explicit offers => offers
    | .at target removed => computeFutureOf left target \ removed
  have hChildResolvedEdge :
      AutomatonFragment.HasResolvedEdge left leftFragment q env label
        (TypeOfferSummary.mk current childFuture) childEdge.target := by
    refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
    · exact hChildEnv
    · exact hChildLabel
    · exact hChildCurrent
    · rfl
  by_cases hAccepting : childEdge.target ∈ leftFragment.accepting
  · have hStateTarget :
        state' = .child 1 (compileType right).initial := by
      rw [← hPendingTarget, hChildEdgeEq]
      simp [sequenceLeftEdge, sequenceRedirectEdge, childState,
        leftFragment, rightFragment, hAccepting, compileType]
    have hResidualTarget : residual' = right := by
      rcases helper_h12_seq_shape alphabet left right hTarget with
        hTargetLeft | hTargetRight
      · rcases hTargetLeft with ⟨leftTarget, qTarget, _hResidualTarget,
          hTargetState,
          _hLeftTargetRelated, _hSurvives⟩
        rw [hStateTarget] at hTargetState
        exact False.elim
          (by
            have hIndex : (1 : Nat) = 0 := by
              simpa [childState, compileType] using hTargetState
            omega)
      · rcases hTargetRight with ⟨qTarget, hTargetState,
          hRightTargetRelated⟩
        have hQ :
            qTarget = (compileType right).initial := by
          rw [hStateTarget] at hTargetState
          simpa [childState] using hTargetState.symm
        rw [hQ] at hRightTargetRelated
        exact relationMembership_functional right (compileType right)
          hRightTargetRelated
          (buildRelationSet_initial right (compileType right))
    have hChildAcceptingPublic :
        childEdge.target ∈ (compileType left).accepting := by
      simpa [compileType, leftFragment] using hAccepting
    have hChildTargetSkip :
        childTargetResidual = .skip childTargetResidual.alphabet :=
      (helper_h13_final_states_represent_completion
        hChildTargetRelated).mp hChildAcceptingPublic
    have hChildTargetRelatedSkip :
        relationMembership (buildRelationSet left (compileType left))
          (.skip childTargetResidual.alphabet) childEdge.target := by
      rw [← hChildTargetSkip]
      exact hChildTargetRelated
    have hChildPublicEdge :
        (compileType left).HasEdge q env label
          (TypeOfferSummary.mk current childFuture) childEdge.target := by
      rw [compileType_hasEdge_iff_hasResolvedEdge left q
        childEdge.target env label (TypeOfferSummary.mk current childFuture)]
      exact hChildResolvedEdge
    by_cases hLabelTock : label = TypeLabel.tock
    · have hChildTock :
          childEdge.label.semantic = TypeLabel.tock := by
        rw [hChildLabel, hLabelTock]
        simp [AutomatonConstructionLabel.semantic]
      have hParentFutureEmpty : future = ∅ := by
        have hResolvedEmpty :
            (match pendingEdge.future with
              | .explicit future => future
              | .at state removed =>
                  computeFutureOf (.seq alphabet left right) state \
                    removed) = ∅ := by
          rw [hChildEdgeEq]
          simp [sequenceLeftEdge, sequenceRedirectEdge,
            sequenceRedirectFutureSpec, hAccepting, hChildTock]
        simpa using hPendingFuture.symm.trans hResolvedEmpty
      exact SeqCompiledEdgeCase.leftFuseTock leftResidual
        childTargetResidual.alphabet q childEdge.target childFuture
        rfl hResidualTarget rfl hLeftSource hChildTargetRelatedSkip
        (by simpa [hLabelTock] using hChildPublicEdge) hLabelTock
        hParentFutureEmpty
    · have hParentFuture :
          future = typeFutureOffers right \ current := by
        simpa [hResidualTarget, hLabelTock] using hFutureEq
      exact SeqCompiledEdgeCase.leftFuse leftResidual
        childTargetResidual.alphabet q childEdge.target childFuture
        rfl hResidualTarget rfl hLeftSource hChildTargetRelatedSkip
        hChildPublicEdge hLabelTock hParentFuture
  · have hStateTarget :
        state' = .child 0 childEdge.target := by
      rw [← hPendingTarget, hChildEdgeEq]
      simp [sequenceLeftEdge, sequenceKeptLeftEdge, childState,
        leftFragment, rightFragment, hAccepting]
    rcases helper_h12_seq_shape alphabet left right hTarget with
      hTargetLeft | hTargetRight
    · rcases hTargetLeft with ⟨leftTarget, qTarget, hResidualTarget,
        hTargetState,
        hLeftTargetRelated, _hSurvives⟩
      have hQ : qTarget = childEdge.target := by
        rw [hStateTarget] at hTargetState
        simpa [childState] using hTargetState.symm
      rw [hQ] at hLeftTargetRelated
      have hChildTargetEq : childTargetResidual = leftTarget :=
        relationMembership_functional left (compileType left)
          hChildTargetRelated hLeftTargetRelated
      rw [hChildTargetEq] at hChildTargetRelated
      have hNonFinal : leftTarget ≠ .skip leftTarget.alphabet := by
        intro hSkip
        have hAcceptingPublic :
            childEdge.target ∈ (compileType left).accepting :=
          (helper_h13_final_states_represent_completion
            hLeftTargetRelated).mpr hSkip
        exact hAccepting (by
          simpa [compileType, leftFragment] using hAcceptingPublic)
      by_cases hLabelTock : label = TypeLabel.tock
      · have hParentFuture : future = ∅ := by
          rw [hFutureEq, if_pos hLabelTock]
        have hChildPublicEdge :
            (compileType left).HasEdge q env label
              (TypeOfferSummary.mk current childFuture) childEdge.target := by
          rw [compileType_hasEdge_iff_hasResolvedEdge left q
            childEdge.target env label (TypeOfferSummary.mk current childFuture)]
          exact hChildResolvedEdge
        exact SeqCompiledEdgeCase.leftStepTock leftResidual leftTarget q
          childEdge.target childFuture rfl hResidualTarget rfl hStateTarget
          hNonFinal hLeftSource hLeftTargetRelated hChildPublicEdge hLabelTock
          hParentFuture
      · have hParentFuture :
            future = typeFutureOffers (.seq alphabet leftTarget right) \ current := by
          rw [hFutureEq, if_neg hLabelTock, hResidualTarget]
        have hChildPublicEdge :
            (compileType left).HasEdge q env label
              (TypeOfferSummary.mk current childFuture) childEdge.target := by
          rw [compileType_hasEdge_iff_hasResolvedEdge left q
            childEdge.target env label (TypeOfferSummary.mk current childFuture)]
          exact hChildResolvedEdge
        exact SeqCompiledEdgeCase.leftStep leftResidual leftTarget q
          childEdge.target childFuture rfl hResidualTarget rfl hStateTarget
          hNonFinal hLeftSource hLeftTargetRelated hChildPublicEdge hLabelTock
          hParentFuture
    · rcases hTargetRight with ⟨qTarget, hTargetState, _hRightTargetRelated⟩
      rw [hStateTarget] at hTargetState
      exact False.elim
        (by
          have hIndex : (0 : Nat) = 1 := by
            simpa [childState] using hTargetState
          omega)

/-- Lifts a non-final left-child edge to a retained public sequence edge. -/
theorem compileType_seq_lift_left_step
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {leftResidual leftTarget : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current childFuture : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        (.seq alphabet leftResidual right) (.child 0 q))
    (_hSource :
      relationMembership (buildRelationSet left (compileType left))
        leftResidual q)
    (hTarget :
      relationMembership (buildRelationSet left (compileType left))
        leftTarget q')
    (hNonFinal : leftTarget ≠ .skip leftTarget.alphabet)
    (hChildStep :
      DecoratedTypeTransition env leftResidual label
        (TypeOfferSummary.mk current childFuture) leftTarget)
    (hNotTock : label ≠ TypeLabel.tock)
    (hChildEdge :
      (compileType left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q') :
    (compileType (.seq alphabet left right)).HasEdge
        (.child 0 q) env label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq alphabet leftTarget right) \ current))
        (.child 0 q') ∧
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        (.seq alphabet leftTarget right) (.child 0 q') := by
  have hChildResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge left q q' env label
      (TypeOfferSummary.mk current childFuture)).mp hChildEdge
  rcases hChildResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, _hPendingFuture,
    hPendingTarget⟩
  have hNotAccepting :
      q' ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting := by
    intro hAccepting
    have hAccepting' : q' ∈ (compileType left).accepting := by
      simpa [compileType] using hAccepting
    exact hNonFinal
      ((helper_h13_final_states_represent_completion hTarget).mp
        hAccepting')
  have hSeqFuture :=
    helper_h15_sequence_left_step_future_offers_agree alphabet left right
      hTarget hNonFinal
  have hParentEdge :
      (compileType (.seq alphabet left right)).HasEdge
        (.child 0 q) env label
        (TypeOfferSummary.mk current
          (typeFutureOffers (.seq alphabet leftTarget right) \ current))
        (.child 0 q') := by
    rw [compileType_hasEdge_iff_hasResolvedEdge
      (.seq alphabet left right)
      (.child 0 q) (.child 0 q') env label
      (TypeOfferSummary.mk current
        (typeFutureOffers (.seq alphabet leftTarget right) \ current))]
    rw [compileTypeFuel_sequence_eq_build alphabet left right]
    have hNotAcceptingPending :
        pendingEdge.target ∉
          (compileTypeFuel (typeCompilationFuel left) left).accepting := by
      rw [hPendingTarget]; exact hNotAccepting
    refine ⟨sequenceKeptLeftEdge
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceLeftEdges,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      refine Or.inl (Or.inl ⟨pendingEdge, ⟨hPendingMem, ?_, hNotAcceptingPending⟩,
        rfl⟩)
      -- The kept-left family now also drops edges out of a deleted left
      -- accepting state; nothing here bounds the source.
      sorry
    · simp [sequenceKeptLeftEdge, childState, hPendingSource]
    · simp [sequenceKeptLeftEdge, hPendingEnv]
    · simp [sequenceKeptLeftEdge, hPendingLabel]
    · simp [sequenceKeptLeftEdge, hPendingCurrent]
    · have hSeqFuture' :
          computeFutureOf (.seq alphabet left right)
              (childState 0 q') =
            typeFutureOffers (.seq alphabet leftTarget right) := by
        simpa [childState] using hSeqFuture
      have hPendingNotTock :
          ¬ pendingEdge.label.semantic = TypeLabel.tock := by
        rw [hPendingLabel]
        simpa [AutomatonConstructionLabel.semantic] using hNotTock
      simp [sequenceKeptLeftEdge, sequenceRedirectFutureSpec, hPendingNotTock,
        hPendingCurrent, hPendingTarget,
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
        childFuture hChildStep.2 hNonFinal hNotTock⟩
  refine ⟨hParentEdge, ?_⟩
  exact relationMembership_seq_left alphabet left right leftTarget hTarget
    hNotAccepting

/-- Lifts a non-final left-child clock edge to a retained public sequence edge.

The clock ends the cycle, so the retained edge exposes no future menu — the
`sequenceRedirectFutureSpec` tock case, mirroring `TypeOffers.seq_tock`. -/
theorem compileType_seq_lift_left_step_tock
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {leftResidual leftTarget : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment}
    {current childFuture : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        (.seq alphabet leftResidual right) (.child 0 q))
    (_hSource :
      relationMembership (buildRelationSet left (compileType left))
        leftResidual q)
    (hTarget :
      relationMembership (buildRelationSet left (compileType left))
        leftTarget q')
    (hNonFinal : leftTarget ≠ .skip leftTarget.alphabet)
    (hChildStep :
      DecoratedTypeTransition env leftResidual TypeLabel.tock
        (TypeOfferSummary.mk current childFuture) leftTarget)
    (hChildEdge :
      (compileType left).HasEdge q env TypeLabel.tock
        (TypeOfferSummary.mk current childFuture) q') :
    (compileType (.seq alphabet left right)).HasEdge
        (.child 0 q) env TypeLabel.tock
        (TypeOfferSummary.mk current ∅)
        (.child 0 q') ∧
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        (.seq alphabet leftTarget right) (.child 0 q') := by
  have hChildResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge left q q' env TypeLabel.tock
      (TypeOfferSummary.mk current childFuture)).mp hChildEdge
  rcases hChildResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, _hPendingFuture,
    hPendingTarget⟩
  have hNotAccepting :
      q' ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting := by
    intro hAccepting
    have hAccepting' : q' ∈ (compileType left).accepting := by
      simpa [compileType] using hAccepting
    exact hNonFinal
      ((helper_h13_final_states_represent_completion hTarget).mp
        hAccepting')
  have hParentEdge :
      (compileType (.seq alphabet left right)).HasEdge
        (.child 0 q) env TypeLabel.tock
        (TypeOfferSummary.mk current ∅)
        (.child 0 q') := by
    rw [compileType_hasEdge_iff_hasResolvedEdge
      (.seq alphabet left right)
      (.child 0 q) (.child 0 q') env TypeLabel.tock
      (TypeOfferSummary.mk current ∅)]
    rw [compileTypeFuel_sequence_eq_build alphabet left right]
    have hNotAcceptingPending :
        pendingEdge.target ∉
          (compileTypeFuel (typeCompilationFuel left) left).accepting := by
      rw [hPendingTarget]; exact hNotAccepting
    refine ⟨sequenceKeptLeftEdge
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceLeftEdges,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      refine Or.inl (Or.inl ⟨pendingEdge, ⟨hPendingMem, ?_, hNotAcceptingPending⟩,
        rfl⟩)
      -- The kept-left family now also drops edges out of a deleted left
      -- accepting state; nothing here bounds the source.
      sorry
    · simp [sequenceKeptLeftEdge, childState, hPendingSource]
    · simp [sequenceKeptLeftEdge, hPendingEnv]
    · simp [sequenceKeptLeftEdge, hPendingLabel]
    · simp [sequenceKeptLeftEdge, hPendingCurrent]
    · have hPendingTock : pendingEdge.label.semantic = TypeLabel.tock := by
        rw [hPendingLabel]
        simp [AutomatonConstructionLabel.semantic]
      simp [sequenceKeptLeftEdge, sequenceRedirectFutureSpec, hPendingCurrent,
        hPendingTock]
    · simp [sequenceKeptLeftEdge, childState, hPendingTarget]
  refine ⟨hParentEdge, ?_⟩
  exact relationMembership_seq_left alphabet left right leftTarget hTarget
    hNotAccepting

/-- Lifts a final left-child edge to the redirected public sequence edge. -/
theorem compileType_seq_lift_left_fuse
     (alphabet skipAlphabet : PactTypeAlphabet)
    (left right : PactType)
    (hDisjoint : right.OfferBranchesDisjoint)
    {leftResidual : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current childFuture : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        (.seq alphabet leftResidual right) (.child 0 q))
    (_hSource :
      relationMembership (buildRelationSet left (compileType left))
        leftResidual q)
    (hTarget :
      relationMembership (buildRelationSet left (compileType left))
        (.skip skipAlphabet) q')
    (hChildStep :
      DecoratedTypeTransition env leftResidual label
        (TypeOfferSummary.mk current childFuture) (.skip skipAlphabet))
    (hNotTock : label ≠ TypeLabel.tock)
    (hChildEdge :
      (compileType left).HasEdge q env label
        (TypeOfferSummary.mk current childFuture) q') :
    (compileType (.seq alphabet left right)).HasEdge
      (.child 0 q) env label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current))
        (.child 1 (compileType right).initial) ∧
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        right (.child 1 (compileType right).initial) := by
  have hChildResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge left q q' env label
      (TypeOfferSummary.mk current childFuture)).mp hChildEdge
  rcases hChildResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, _hPendingFuture,
    hPendingTarget⟩
  have hAccepting :
      q' ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting := by
    have hAccepting' : q' ∈ (compileType left).accepting :=
      (helper_h13_final_states_represent_completion hTarget).mpr rfl
    simpa [compileType] using hAccepting'
  have hSeqFuture :=
    helper_h15_sequence_left_fuse_future_offers_agree alphabet
      skipAlphabet left right hDisjoint hTarget
  have hParentEdge :
      (compileType (.seq alphabet left right)).HasEdge
        (.child 0 q) env label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current))
        (.child 1 (compileType right).initial) := by
    rw [compileType_hasEdge_iff_hasResolvedEdge
      (.seq alphabet left right)
      (.child 0 q) (.child 1 (compileType right).initial) env label
      (TypeOfferSummary.mk current (typeFutureOffers right \ current))]
    rw [compileTypeFuel_sequence_eq_build alphabet left right]
    refine ⟨sequenceRedirectEdge
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceRedirectEdges,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      refine Or.inr ⟨pendingEdge,
        ⟨hPendingMem, ?_, hPendingTarget ▸ hAccepting⟩, rfl⟩
      sorry
    · simp [sequenceRedirectEdge, childState, hPendingSource]
    · simp [sequenceRedirectEdge, hPendingEnv]
    · simp [sequenceRedirectEdge, hPendingLabel]
    · simp [sequenceRedirectEdge, hPendingCurrent]
    · have hSeqFuture' :
          computeFutureOf (.seq alphabet left right)
              (childState 1
                (compileTypeFuel (typeCompilationFuel right) right).initial) =
            typeFutureOffers right := by
        simpa [compileType, childState] using hSeqFuture
      have hPendingNotTock :
          pendingEdge.label.semantic ≠ TypeLabel.tock := by
        rw [hPendingLabel]
        simpa [AutomatonConstructionLabel.semantic] using hNotTock
      simp [sequenceRedirectEdge, sequenceRedirectFutureSpec, hPendingCurrent,
        hPendingNotTock, hSeqFuture']
    · simp [sequenceRedirectEdge, compileType, childState]
  have hParentStep :
      DecoratedTypeTransition env (.seq alphabet leftResidual right) label
        (TypeOfferSummary.mk current (typeFutureOffers right \ current))
        right :=
    ⟨TypeTransition.seq_fuse env alphabet skipAlphabet leftResidual right label
        hChildStep.1,
      TypeOffers.seq_fuse env alphabet skipAlphabet leftResidual right label
        current childFuture hChildStep.2 hNotTock⟩
  refine ⟨hParentEdge, ?_⟩
  exact relationMembership_seq_right alphabet left right right
    (buildRelationSet_initial right (compileType right))

/-- Lifts a final left-child clock edge to the redirected public sequence edge
with empty future offers. -/
theorem compileType_seq_lift_left_fuse_tock
     (alphabet skipAlphabet : PactTypeAlphabet)
    (left right : PactType)
    {leftResidual : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment}
    {current childFuture : Finset BareMessage}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        (.seq alphabet leftResidual right) (.child 0 q))
    (_hSource :
      relationMembership (buildRelationSet left (compileType left))
        leftResidual q)
    (hTarget :
      relationMembership (buildRelationSet left (compileType left))
        (.skip skipAlphabet) q')
    (hChildStep :
      DecoratedTypeTransition env leftResidual TypeLabel.tock
        (TypeOfferSummary.mk current childFuture) (.skip skipAlphabet))
    (hChildEdge :
      (compileType left).HasEdge q env TypeLabel.tock
        (TypeOfferSummary.mk current childFuture) q') :
    (compileType (.seq alphabet left right)).HasEdge
      (.child 0 q) env TypeLabel.tock
        (TypeOfferSummary.mk current ∅)
        (.child 1 (compileType right).initial) ∧
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        right (.child 1 (compileType right).initial) := by
  have hChildResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge left q q' env TypeLabel.tock
      (TypeOfferSummary.mk current childFuture)).mp hChildEdge
  rcases hChildResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, _hPendingFuture,
    hPendingTarget⟩
  have hAccepting :
      q' ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting := by
    have hAccepting' : q' ∈ (compileType left).accepting :=
      (helper_h13_final_states_represent_completion hTarget).mpr rfl
    simpa [compileType] using hAccepting'
  have hParentEdge :
      (compileType (.seq alphabet left right)).HasEdge
        (.child 0 q) env TypeLabel.tock
        (TypeOfferSummary.mk current ∅)
        (.child 1 (compileType right).initial) := by
    rw [compileType_hasEdge_iff_hasResolvedEdge
      (.seq alphabet left right)
      (.child 0 q) (.child 1 (compileType right).initial)
      env TypeLabel.tock (TypeOfferSummary.mk current ∅)]
    rw [compileTypeFuel_sequence_eq_build alphabet left right]
    refine ⟨sequenceRedirectEdge
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      pendingEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceRedirectEdges,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      refine Or.inr ⟨pendingEdge,
        ⟨hPendingMem, ?_, hPendingTarget ▸ hAccepting⟩, rfl⟩
      sorry
    · simp [sequenceRedirectEdge, childState, hPendingSource]
    · simp [sequenceRedirectEdge, hPendingEnv]
    · simp [sequenceRedirectEdge, hPendingLabel]
    · simp [sequenceRedirectEdge, hPendingCurrent]
    · have hPendingTock : pendingEdge.label.semantic = TypeLabel.tock := by
        rw [hPendingLabel]
        simp [AutomatonConstructionLabel.semantic]
      simp [sequenceRedirectEdge, sequenceRedirectFutureSpec, hPendingCurrent,
        hPendingTock]
    · simp [sequenceRedirectEdge, compileType, childState]
  refine ⟨hParentEdge, ?_⟩
  exact relationMembership_seq_right alphabet left right right
    (buildRelationSet_initial right (compileType right))

/-- Lifts a right-child edge to a copied public sequence edge. -/
theorem compileType_seq_lift_right_step
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hDisjoint : right.OfferBranchesDisjoint)
    {rightResidual rightTarget : PactType}
    {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hParentSource :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        rightResidual (.child 1 q))
    (_hSource :
      relationMembership (buildRelationSet right (compileType right))
        rightResidual q)
    (_hTarget :
      relationMembership (buildRelationSet right (compileType right))
        rightTarget q')
    (hChildStep :
      DecoratedTypeTransition env rightResidual label offers rightTarget)
    (hChildEdge :
      (compileType right).HasEdge q env label offers q') :
    ∃ state',
      (compileType (.seq alphabet left right)).HasEdge
        (.child 1 q) env label
        offers state' ∧
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        rightTarget state' := by
  have hChildResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge right q q' env label
      offers).mp hChildEdge
  rcases hChildResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
    hPendingEnv, hPendingLabel, hPendingCurrent, hPendingFuture,
    hPendingTarget⟩
  have hParentEdge :
      (compileType (.seq alphabet left right)).HasEdge
        (.child 1 q) env label
        offers (.child 1 q') := by
    rw [compileType_hasEdge_iff_hasResolvedEdge
      (.seq alphabet left right)
      (.child 1 q) (.child 1 q') env label offers]
    rw [compileTypeFuel_sequence_eq_build alphabet left right]
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
          have hStateMem := compileTypeFuel_futureTargetsInStates
            (typeCompilationFuel right) right le_rfl hDisjoint pendingEdge
            hPendingMem futureTarget removed hSpec
          have hSeqFuture :=
            computeFutureOf_sequence_right alphabet left right hDisjoint
              futureTarget hStateMem
          have hSeqFuture' :
              computeFutureOf (.seq alphabet left right)
                  (childState 1 futureTarget) =
                computeFutureOf right futureTarget := by
            simpa [childState] using hSeqFuture
          simpa [childPendingEdge, childFutureSpec, hSpec, hSeqFuture'] using
            hPendingFuture
    · simp [childPendingEdge, childState, hPendingTarget]
  refine ⟨.child 1 q', hParentEdge, ?_⟩
  exact relationMembership_seq_right alphabet left right rightTarget
    _hTarget

/-- Proves every related sequence pair has the sequence shape, given the forward direction of the left child's own step correspondence. -/
lemma relationMembership_seq_cases
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        residual state) :
    seqRelationShape alphabet left right (residual, state) := by
  rcases helper_h12_seq_shape alphabet left right hRelated with
    hLeft | hRight
  · rcases hLeft with ⟨residualLeft, q1, hResidual, hState,
      hLeftRelated, hSurvives⟩
    exact Or.inl ⟨q1, residualLeft, by simp [hResidual, hState],
      hLeftRelated, hSurvives⟩
  · rcases hRight with ⟨q2, hState, hRightRelated⟩
    exact Or.inr ⟨q2, by simpa using hState, hRightRelated⟩

/-- Proves every public sequence edge leaving a related state belongs to one of the sequence edge families. -/
theorem compileType_seq_edge_cases
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hDisjoint : right.OfferBranchesDisjoint)
    {residual residual' : PactType}
    {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        residual state)
    (hEdge :
      (compileType (.seq alphabet left right)).HasEdge state env label
        (TypeOfferSummary.mk current future) state')
    (hTarget :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType (.seq alphabet left right)))
        residual' state') :
    SeqCompiledEdgeCase alphabet left right residual residual' state state'
      env label current future := by
  rcases relationMembership_seq_cases alphabet left right hRelated with
    hLeft | hRight
  · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _hSurvives⟩
    cases hEntry
    exact helper_h15_sequence_left_public_edge_cases alphabet left right
      hRelated hLeftRelated hEdge hTarget
  · rcases hRight with ⟨q, hState, hRightRelated⟩
    simp only at hState hRightRelated
    subst state
    have hResolved :=
      (compileType_hasEdge_iff_hasResolvedEdge
        (.seq alphabet left right)
        (.child 1 q) state' env label
        (TypeOfferSummary.mk current future)).mp hEdge
    rw [compileTypeFuel_sequence_eq_build alphabet left right]
      at hResolved
    rcases hResolved with ⟨pendingEdge, hPendingMem, hPendingSource,
      hPendingEnv, hPendingLabel, hPendingCurrent, hPendingFuture,
      hPendingTarget⟩
    obtain ⟨childEdge, hChildEdgeMem, hChildSource, hChildEdgeEq⟩ :=
      (buildSequenceAutomaton_outgoing_right
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right)
        q pendingEdge).mp ⟨hPendingMem, hPendingSource⟩
    have hTargetState : state' = .child 1 childEdge.target := by
      rw [← hPendingTarget, hChildEdgeEq]
      rfl
    have hRightTargetRelated :
        relationMembership (buildRelationSet right (compileType right))
          residual' childEdge.target := by
      rcases relationMembership_seq_cases alphabet left right hTarget with
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
        (compileType right).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
      rw [compileType_hasEdge_iff_hasResolvedEdge right q
        childEdge.target env label (TypeOfferSummary.mk current future)]
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
            have hStateMem := compileTypeFuel_futureTargetsInStates
              (typeCompilationFuel right) right le_rfl hDisjoint childEdge
              hChildEdgeMem futureTarget removed hSpec
            have hSeqFuture :=
              computeFutureOf_sequence_right alphabet left right hDisjoint
                futureTarget
                hStateMem
            have hSeqFuture' :
                computeFutureOf (.seq alphabet left right)
                    (childState 1 futureTarget) =
                  computeFutureOf right futureTarget := by
              simpa [childState] using hSeqFuture
            simpa [hChildEdgeEq, childPendingEdge, childFutureSpec, hSpec,
              hSeqFuture'] using hPendingFuture
    exact SeqCompiledEdgeCase.rightStep q childEdge.target rfl hTargetState
      hRightRelated hRightTargetRelated hChildEdge

end

end Pact
