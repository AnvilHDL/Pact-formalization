import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.ChoiceRelations

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
        (compileTypeFuel (typeCompilationFuel right) right)
        (computeFutureOfFuel (typeCompilationFuel left) left)
        (fun state => decide (∃ entry ∈ buildRelationSetCoreFuel
            (typeCompilationFuel left) left,
          entry.2 = state ∧
            typeCanCompleteThisCycleFuel (sizeOf entry.1 + 1) entry.1 = true)) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  rw [compileTypeFuel.eq_def]
  simp only [Nat.min_eq_right (le_max_left _ _)]
  rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
    compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]

theorem buildSequenceAutomaton_menuStep_right
     (left right : AutomatonFragment)
    {leftFuture : TypeAutomatonState → Finset BareMessage}
    {leftCompletes : TypeAutomatonState → Bool}
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton left right leftFuture leftCompletes
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.menuStep (.child 1 state) =
      (child.menuStep state).image (.child 1) := by
  exact menuStep_of_outgoing_childPendingEdge _ right 1 state
    (buildSequenceAutomaton_outgoing_right left right state)

theorem buildSequenceAutomaton_offersAt_right
     (left right : AutomatonFragment)
    {leftFuture : TypeAutomatonState → Finset BareMessage}
    {leftCompletes : TypeAutomatonState → Bool}
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton left right leftFuture leftCompletes
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
    simpa [childPendingEdge] using hOffer
  · intro hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction ⊢
    rcases hAction with
      ⟨childEdge, ⟨hChildEdgeMem, hChildSource⟩, hOffer⟩
    refine ⟨childPendingEdge 1 childEdge, ?_, ?_⟩
    · exact (buildSequenceAutomaton_outgoing_right left right state
        (childPendingEdge 1 childEdge)).mpr
          ⟨childEdge, hChildEdgeMem, hChildSource, rfl⟩
    · simpa [childPendingEdge] using hOffer

/-- Proves a `.child 1`-tagged state's future menu, in a compiled sequence, agrees with the right child's own. -/
theorem computeFutureOf_sequence_right
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = alphabet)
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
    (computeFutureOfFuel (typeCompilationFuel left) left)
    (fun state => decide (∃ entry ∈ buildRelationSetCoreFuel
        (typeCompilationFuel left) left,
      entry.2 = state ∧
        typeCanCompleteThisCycleFuel (sizeOf entry.1 + 1) entry.1 = true))
  have hCard : rightFragment.states.card ≤ sequence.states.card := by
    have hTaggedCard :
        (childStates 1 rightFragment).card = rightFragment.states.card := by
      unfold childStates
      apply Finset.card_image_of_injective
      intro first second hEq
      simpa [childState] using hEq
    rw [← hTaggedCard]
    apply Finset.card_le_card
    intro tagged hTagged
    simp only [sequence, buildSequenceAutomaton, finishAutomatonFragment,
      Finset.mem_union]
    exact Or.inr hTagged
  have hSequenceFuel : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  have hInfo : ∀ visited,
      stateProductInfo (.seq alphabet left right) (.child 1 visited) =
        stateProductInfo right visited := by
    intro visited
    unfold stateProductInfo
    rw [hSequenceFuel]
    simp only [stateProductInfoFuel]
    exact stateProductInfoFuel_eq_of_sufficient right visited
      (le_max_right _ _) le_rfl
  unfold computeFutureOf
  exact computeFutureOfFuel_child_embedding (.seq alphabet left right) right
    (typeCompilationFuel (.seq alphabet left right)) (typeCompilationFuel right)
    sequence rightFragment 1
    (compileTypeFuel_sequence_eq_build alphabet left right) rfl
    le_rfl le_rfl hDisjoint hRightAlphabet
    (by rw [hSequenceFuel]; omega) hInfo
    (buildSequenceAutomaton_outgoing_right leftFragment rightFragment)
    hCard state hState (menuDependencyTargets_seq_right alphabet left right)

/- Previous proof for saturation without menu dependencies.
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
  rw [show right.alphabet = (PactType.seq alphabet left right).alphabet from by
    rw [hRightAlphabet]; rfl]
  refine congrArg (Finset.filter _) ?_
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
-/

/-- Every edge leaving a retained left state is a rewritten left edge. -/
theorem buildSequenceAutomaton_outgoing_left
     (left right : AutomatonFragment)
    {leftFuture : TypeAutomatonState → Finset BareMessage}
    {leftCompletes : TypeAutomatonState → Bool}
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge)
    (hOutgoing :
      edge ∈ (buildSequenceAutomaton left right leftFuture leftCompletes).edges ∧
        edge.source = .child 0 state) :
    ∃ childEdge ∈ left.edges,
      childEdge.source = state ∧
        edge = sequenceLeftEdge left right leftFuture leftCompletes childEdge := by
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
      future = (childFuture ∪ sequenceRightMenu source right) \ current →
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
      future = (childFuture ∪ sequenceRightMenu source right) \ current →
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

end

end Pact
