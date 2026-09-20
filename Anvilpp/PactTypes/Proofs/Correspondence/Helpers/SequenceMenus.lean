import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.Parallel
import Anvilpp.PactTypes.Spec.Automata.SequenceMenuLemmas

namespace Pact

noncomputable section

open Classical

variable {leftFuture : TypeAutomatonState → Finset BareMessage}
  {leftCompletes : TypeAutomatonState → Bool}

/-- A retained source keeps every left edge, redirecting final targets. -/
theorem sequenceLeftEdge_mem (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ left.edges)
    (hRetained : edge.source ∉ sequenceDeleted left) :
    sequenceLeftEdge left right leftFuture leftCompletes edge ∈ (buildSequenceAutomaton left right leftFuture leftCompletes).edges := by
  by_cases hFinal : edge.target ∈ left.accepting
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨edge, Finset.mem_filter.mpr ⟨hEdge, hRetained, hFinal⟩,
        by simp [sequenceLeftEdge, hFinal]⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr
      ⟨edge, Finset.mem_filter.mpr ⟨hEdge, hRetained, hFinal⟩,
        by simp [sequenceLeftEdge, hFinal]⟩

@[simp] theorem sequenceLeftEdge_future (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right leftFuture leftCompletes edge).future =
      sequenceLeftFutureSpec edge.label (childState 1 right.initial)
        (resolveFutureSpec leftFuture edge.future) edge.current (leftCompletes edge.source) := by
  by_cases hFinal : edge.target ∈ left.accepting <;>
    simp [sequenceLeftEdge, sequenceRedirectEdge, sequenceKeptLeftEdge,
      hFinal]

/-- A retained left source redirects exactly its child's non-clock targets. -/
theorem buildSequenceAutomaton_menuStep_left
    (left right : AutomatonFragment)
    (source : TypeAutomatonState) (hRetained : source ∉ sequenceDeleted left) :
    (⟨(buildSequenceAutomaton left right leftFuture leftCompletes).states,
      (buildSequenceAutomaton left right leftFuture leftCompletes).edges⟩ : PendingAutomaton).menuStep
        (.child 0 source) =
      ((⟨left.states, left.edges⟩ : PendingAutomaton).menuStep source).image
        (sequenceRedirect left right) := by
  ext target
  simp only [PendingAutomaton.menuStep, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hReference⟩
    obtain ⟨childEdge, hChild, hSource, rfl⟩ :=
      buildSequenceAutomaton_outgoing_left left right source edge hEdge
    by_cases hClock : childEdge.label.semantic = .tock
    · simp [hClock] at hReference
    · have hTarget : target = sequenceRedirect left right childEdge.target := by
        simpa [hClock] using hReference
      exact ⟨childEdge.target,
        ⟨childEdge, ⟨hChild, hSource⟩, by simp [hClock]⟩, hTarget.symm⟩
  · rintro ⟨childTarget, ⟨edge, ⟨hEdge, hSource⟩, hReference⟩, rfl⟩
    by_cases hClock : edge.label.semantic = .tock
    · simp [hClock] at hReference
    · have hEq : childTarget = edge.target := by simpa [hClock] using hReference
      refine ⟨sequenceLeftEdge left right leftFuture leftCompletes edge,
        ⟨sequenceLeftEdge_mem left right edge hEdge (hSource ▸ hRetained),
          by simp [hSource, childState]⟩, ?_⟩
      simp [hClock, hEq]

/-- Every edge from a retained left final enters the right copy. -/
theorem buildSequenceAutomaton_menuStep_left_final
    (left right : AutomatonFragment) (hInert : left.AcceptingInert)
    (source : TypeAutomatonState) (hFinal : source ∈ left.accepting) :
    (⟨(buildSequenceAutomaton left right leftFuture leftCompletes).states,
      (buildSequenceAutomaton left right leftFuture leftCompletes).edges⟩ : PendingAutomaton).menuStep
        (.child 0 source) ⊆ {TypeAutomatonState.child 1 right.initial} := by
  intro target hTarget
  simp only [PendingAutomaton.menuStep, Finset.mem_biUnion, Finset.mem_filter] at hTarget
  obtain ⟨edge, hEdge, hReference⟩ := hTarget
  obtain ⟨childEdge, hChild, hSource, rfl⟩ :=
    buildSequenceAutomaton_outgoing_left left right source edge hEdge
  have hTargetFinal := (hInert childEdge hChild (hSource ▸ hFinal)).2.1
  by_cases hClock : childEdge.label.semantic = .tock
  · simp [hClock] at hReference
  · simpa [sequenceRedirect, hClock, hTargetFinal, childState] using hReference

/-- Rewriting a left edge preserves its current offer. -/
theorem buildSequenceAutomaton_offersAt_left
    (left right : AutomatonFragment)
    (source : TypeAutomatonState) (hRetained : source ∉ sequenceDeleted left) :
    (⟨(buildSequenceAutomaton left right leftFuture leftCompletes).states,
      (buildSequenceAutomaton left right leftFuture leftCompletes).edges⟩ : PendingAutomaton).offersAt
        (.child 0 source) =
      (⟨left.states, left.edges⟩ : PendingAutomaton).offersAt source := by
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨edge, hEdge, hOfferEdge⟩
    obtain ⟨childEdge, hChild, hSource, rfl⟩ :=
      buildSequenceAutomaton_outgoing_left left right source edge hEdge
    exact ⟨childEdge, ⟨hChild, hSource⟩, by simpa using hOfferEdge⟩
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hOfferEdge⟩
    exact ⟨sequenceLeftEdge left right leftFuture leftCompletes edge,
      ⟨sequenceLeftEdge_mem left right edge hEdge (hSource ▸ hRetained),
        by simp [hSource, childState]⟩, by simpa using hOfferEdge⟩

/-- Finals carry the true completion flag in the canonical relation. -/
theorem accepting_state_completionFlag (fuel : Nat) (processType : PactType)
    (hFuel : typeCompilationFuel processType ≤ fuel)
    (source : TypeAutomatonState)
    (hFinal : source ∈ (compileTypeFuel fuel processType).accepting) :
    ∃ residual, (residual, source) ∈ buildRelationSetCoreFuel fuel processType ∧
      typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true := by
  rw [compileTypeFuel_eq_of_sufficient processType hFuel le_rfl] at hFinal
  obtain ⟨alphabet, hRelated⟩ := relationMembership_of_accepting processType hFinal
  refine ⟨.skip alphabet, ?_, rfl⟩
  rw [buildRelationSetCoreFuel_eq_of_sufficient processType hFuel le_rfl]
  exact hRelated

/-- The paper's left-reference equation includes inherited and optimistic links. -/
theorem compiledMenuGraphFuel_sequence_left_references
    (fuel : Nat) (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftFuel : typeCompilationFuel left ≤ fuel)
    (hRightFuel : typeCompilationFuel right ≤ fuel)
    (source : TypeAutomatonState)
    (hRetained : source ∉ sequenceDeleted (compileTypeFuel fuel left)) :
    (compiledMenuGraphFuel (fuel + 1) (.seq alphabet left right)).referencedStates
        (.child 0 source) =
      ((compiledMenuGraphFuel fuel left).referencedStates source).image
        (sequenceRedirect (compileTypeFuel fuel left) (compileTypeFuel fuel right)) ∪
      if ∃ residual, (residual, source) ∈ buildRelationSetCoreFuel fuel left ∧
          typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true then
        {TypeAutomatonState.child 1 (compileTypeFuel fuel right).initial}
      else ∅ := by
  have hParentFuel : typeCompilationFuel (.seq alphabet left right) ≤ fuel + 1 := by
    simp only [typeCompilationFuel]
    omega
  have hParentLinks := compileTypeMenuLinksFuel_eq_of_sufficient
    (.seq alphabet left right) hParentFuel le_rfl
  have hLeftLinks := compileTypeMenuLinksFuel_eq_of_sufficient left hLeftFuel le_rfl
  simp only [compiledMenuGraphFuel, Nat.min_eq_right hParentFuel,
    Nat.min_eq_right hLeftFuel, PendingAutomaton.withMenuDependencies]
  rw [← hParentLinks, ← hLeftLinks, menuDependencyTargets_seq_left
    fuel alphabet left right source hRetained]
  rw [compileTypeFuel, buildSequenceAutomaton_menuStep_left
    (compileTypeFuel fuel left) (compileTypeFuel fuel right) source hRetained,
    Finset.image_union]
  exact (Finset.union_assoc _ _ _).symm

/-- The fixed contribution at a state: direct offers and the product clause. -/
def compiledMenuContribution (processType : PactType)
    (state : TypeAutomatonState) : Finset BareMessage :=
  let fragment := compileTypeFuel (typeCompilationFuel processType) processType
  (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).offersAt state ∪
    match stateProductInfo processType state with
    | some (interface, left, right, q1, q2) =>
        hideTypeOffers interface
          (computeFutureOf left q1 ∪ computeFutureOf right q2)
    | none => ∅

/-- Fuel stability identifies the compiler's menu with saturation of these contributions. -/
theorem computeFutureOf_eq_menuFrom (processType : PactType)
    (state : TypeAutomatonState) :
    computeFutureOf processType state =
      ((compiledMenuGraphFuel (typeCompilationFuel processType) processType).menuFrom
        (compiledMenuContribution processType) state).filter
          (fun action => action ∈ processType.alphabet.actions) := by
  obtain ⟨fuel, hFuel⟩ : ∃ fuel, typeCompilationFuel processType = fuel + 1 :=
    ⟨typeCompilationFuel processType - 1, by
      have := typeCompilationFuel_positive processType
      omega⟩
  unfold computeFutureOf
  rw [hFuel, computeFutureOfFuel]
  unfold FiniteMenuGraph.menuFrom compiledMenuGraphFuel
  rw [hFuel]
  apply congrArg (Finset.filter _)
  apply Finset.biUnion_congr rfl
  intro visited _
  unfold compiledMenuContribution
  rw [hFuel]
  congr 1
  cases hInfo : stateProductInfo processType visited with
  | none => rfl
  | some info =>
      obtain ⟨interface, left, right, q1, q2⟩ := info
      have hInfoFuel : stateProductInfoFuel (typeCompilationFuel processType)
          processType visited = some (interface, left, right, q1, q2) := hInfo
      obtain ⟨hLeft, hRight⟩ := stateProductInfoFuel_component_fuel_lt
        _ _ _ _ _ _ _ _ (typeCompilationFuel_sufficient processType) hInfoFuel
      have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
        simp only [TypeCompilationFuelSufficient]
        rw [hFuel] at hLeft
        omega
      have hRightFuel : TypeCompilationFuelSufficient right fuel := by
        simp only [TypeCompilationFuelSufficient]
        rw [hFuel] at hRight
        omega
      simp only
      rw [computeFutureOfFuel_eq_of_sufficient left q1 hLeftFuel le_rfl,
        computeFutureOfFuel_eq_of_sufficient right q2 hRightFuel le_rfl]
      rfl

/-- The retained left copy preserves the product clause as well as direct offers. -/
theorem compiledMenuContribution_sequence_left
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState)
    (hRetained : source ∉ sequenceDeleted
      (compileTypeFuel (typeCompilationFuel left) left)) :
    compiledMenuContribution (.seq alphabet left right) (.child 0 source) =
      compiledMenuContribution left source := by
  have hInfo : stateProductInfo (.seq alphabet left right) (.child 0 source) =
      stateProductInfo left source := by
    unfold stateProductInfo
    rw [show typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 by
        simp only [typeCompilationFuel]; omega]
    simp only [stateProductInfoFuel]
    exact stateProductInfoFuel_eq_of_sufficient left source (le_max_left _ _) le_rfl
  unfold compiledMenuContribution
  rw [compileTypeFuel_sequence_eq_build]
  dsimp only
  rw [buildSequenceAutomaton_offersAt_left
    _ _ source hRetained, hInfo]

/-- The right copy preserves the same fixed contribution. -/
theorem compiledMenuContribution_sequence_right
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState) :
    compiledMenuContribution (.seq alphabet left right) (.child 1 source) =
      compiledMenuContribution right source := by
  have hInfo : stateProductInfo (.seq alphabet left right) (.child 1 source) =
      stateProductInfo right source := by
    unfold stateProductInfo
    rw [show typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 by
        simp only [typeCompilationFuel]; omega]
    simp only [stateProductInfoFuel]
    exact stateProductInfoFuel_eq_of_sufficient right source (le_max_right _ _) le_rfl
  unfold compiledMenuContribution
  rw [compileTypeFuel_sequence_eq_build]
  dsimp only
  rw [buildSequenceAutomaton_offersAt_right, hInfo]

/-- A final contributes neither direct offers nor a product menu. -/
theorem compiledMenuContribution_accepting (processType : PactType)
    (source : TypeAutomatonState)
    (hFinal : source ∈ (compileTypeFuel (typeCompilationFuel processType)
      processType).accepting) :
    compiledMenuContribution processType source = ∅ := by
  unfold compiledMenuContribution
  dsimp only
  rw [acceptingInert_offersAt_empty _ (compileTypeFuel_acceptingInert _ processType)
    source hFinal]
  have hInfo := compileTypeFuel_accepting_stateProductInfoFuel_none
    (typeCompilationFuel processType) processType source hFinal
  change stateProductInfo processType source = none at hInfo
  simp [hInfo]

/-- Once compilation fuel suffices, the menu-reference graph is unchanged. -/
theorem compiledMenuGraphFuel_eq_of_sufficient (processType : PactType)
    {first second : Nat} (hFirst : typeCompilationFuel processType ≤ first)
    (hSecond : typeCompilationFuel processType ≤ second) :
    compiledMenuGraphFuel first processType = compiledMenuGraphFuel second processType := by
  simp only [compiledMenuGraphFuel, Nat.min_eq_right hFirst, Nat.min_eq_right hSecond]
  rw [compileTypeFuel_eq_of_sufficient processType hFirst hSecond]

/-- The sequence path decomposition for arbitrary observations. This also
applies to marker sources; it does not add edges or menu dependencies. -/
theorem compiledMenuFrom_sequence_left
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (leftOffer rightOffer parentOffer : TypeAutomatonState → Finset BareMessage)
    (source : TypeAutomatonState)
    (hSource : source ∈ (compileTypeFuel (typeCompilationFuel left) left).states)
    (hRetained : source ∉ sequenceDeleted
      (compileTypeFuel (typeCompilationFuel left) left))
    (hComplete : ∀ q ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).futureReachable source,
      ∀ r ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).referencedStates q,
      (∃ residual, (residual, r) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true) →
      ∃ residual, (residual, q) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true)
    (hFinalEmpty : ∀ q ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting,
      leftOffer q = ∅)
    (hLeftOffer : ∀ q ∈ (compileTypeFuel (typeCompilationFuel left) left).states,
      q ∉ sequenceDeleted (compileTypeFuel (typeCompilationFuel left) left) →
        parentOffer (.child 0 q) = leftOffer q)
    (hRightOffer : ∀ q ∈ (compileTypeFuel (typeCompilationFuel right) right).states,
      parentOffer (.child 1 q) = rightOffer q) :
    (compiledMenuGraphFuel (typeCompilationFuel (.seq alphabet left right))
      (.seq alphabet left right)).menuFrom parentOffer (.child 0 source) =
      (compiledMenuGraphFuel (typeCompilationFuel left) left).menuFrom leftOffer source ∪
        if ∃ residual, (residual, source) ∈
            buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
            typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true then
          (compiledMenuGraphFuel (typeCompilationFuel right) right).menuFrom rightOffer
            (compileTypeFuel (typeCompilationFuel right) right).initial
        else ∅ := by
  let leftFragment := compileTypeFuel (typeCompilationFuel left) left
  let rightFragment := compileTypeFuel (typeCompilationFuel right) right
  let leftGraph := compiledMenuGraphFuel (typeCompilationFuel left) left
  let rightGraph := compiledMenuGraphFuel (typeCompilationFuel right) right
  let parentGraph := compiledMenuGraphFuel
    (typeCompilationFuel (.seq alphabet left right)) (.seq alphabet left right)
  let complete := fun q => decide (∃ residual,
    (residual, q) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
      typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true)
  have hFuel : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hLeftClosed := compiledMenuGraphFuel_referencesClosed
    (typeCompilationFuel left) left le_rfl hLeftDisjoint
  have hRightClosed := compiledMenuGraphFuel_referencesClosed
    (typeCompilationFuel right) right le_rfl hRightDisjoint
  have hParentClosed := compiledMenuGraphFuel_referencesClosed
    (typeCompilationFuel (.seq alphabet left right)) (.seq alphabet left right) le_rfl
    (show (PactType.seq alphabet left right).OfferBranchesDisjoint from
      by simpa only [PactType.OfferBranchesDisjoint] using And.intro hLeftDisjoint hRightDisjoint)
  have hLeftStates : ∀ q ∈ leftGraph.states, q ∉ sequenceDeleted leftFragment →
      TypeAutomatonState.child 0 q ∈ parentGraph.states := by
    intro q hq hRetained
    change _ ∈ (compileTypeFuel _ _).states
    rw [compileTypeFuel_sequence_eq_build]
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨q, Finset.mem_sdiff.mpr ⟨hq, hRetained⟩, rfl⟩
  have hRightStates : ∀ q ∈ rightGraph.states,
      TypeAutomatonState.child 1 q ∈ parentGraph.states := by
    intro q hq
    change _ ∈ (compileTypeFuel _ _).states
    rw [compileTypeFuel_sequence_eq_build]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hFinalClosed : ∀ q ∈ leftFragment.accepting,
      leftGraph.referencedStates q ⊆ leftFragment.accepting := by
    intro q hq
    change (⟨leftFragment.states, leftFragment.edges⟩ : PendingAutomaton).menuStep q ∪
      menuDependencyTargets _ q ⊆ _
    simp only [Nat.min_self, compileTypeMenuLinksFuel_accepting
      (typeCompilationFuel left) left q hq, Finset.union_empty]
    exact acceptingInert_menuStep_subset _ (compileTypeFuel_acceptingInert _ left) q hq
  have hLeftReferences : ∀ q ∈ leftGraph.states, q ∉ sequenceDeleted leftFragment →
      parentGraph.referencedStates (.child 0 q) =
        (leftGraph.referencedStates q).image (sequenceRedirect leftFragment rightFragment) ∪
          if complete q then {TypeAutomatonState.child 1 rightFragment.initial} else ∅ := by
    intro q _ hq
    have hqShared : q ∉ sequenceDeleted
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left) := by
      rwa [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl]
    have hRefs := compiledMenuGraphFuel_sequence_left_references
      (max (typeCompilationFuel left) (typeCompilationFuel right)) alphabet left right
      (le_max_left _ _) (le_max_right _ _) q hqShared
    rw [compiledMenuGraphFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl,
      buildRelationSetCoreFuel_eq_of_sufficient left (le_max_left _ _) le_rfl] at hRefs
    simpa only [parentGraph, leftGraph, leftFragment, rightFragment, complete,
      hFuel, decide_eq_true_eq] using hRefs
  have hRightReferences : ∀ q, parentGraph.referencedStates (.child 1 q) =
      (rightGraph.referencedStates q).image (.child 1) := by
    intro q
    change (⟨(compileTypeFuel _ _).states, (compileTypeFuel _ _).edges⟩ :
      PendingAutomaton).menuStep (.child 1 q) ∪ menuDependencyTargets _ _ = _
    rw [compileTypeFuel_sequence_eq_build]
    simp only [Nat.min_self]
    rw [buildSequenceAutomaton_menuStep_right,
      menuDependencyTargets_seq_right alphabet left right]
    simp only [rightGraph, compiledMenuGraphFuel, PendingAutomaton.withMenuDependencies,
      Nat.min_self, Finset.image_union]
  have hMenus := FiniteMenuGraph.menuFrom_sequence_left leftGraph rightGraph parentGraph
    leftFragment.accepting (sequenceDeleted leftFragment) rightFragment.initial source complete
    leftOffer rightOffer parentOffer
    hLeftClosed hRightClosed hParentClosed hSource hRetained
    (compileTypeFuel_initial_mem _ right (typeCompilationFuel_sufficient right))
    (fun _ h => (Finset.mem_sdiff.mp h).1) hLeftStates hRightStates hFinalClosed
    hFinalEmpty
    (fun q hq => by
      simpa only [complete, decide_eq_true_eq] using
        accepting_state_completionFlag (typeCompilationFuel left) left le_rfl q hq)
    (fun q hq r hr hc => by
      simp only [complete, decide_eq_true_eq] at hc ⊢
      exact hComplete q hq r hr hc)
    hLeftReferences hRightReferences
    hLeftOffer hRightOffer
  simpa only [complete, decide_eq_true_eq] using hMenus

/-- The sequence equation, with the paper's backward completion invariant explicit. -/
theorem computeFutureOf_sequence_left
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (source : TypeAutomatonState)
    (hSource : source ∈ (compileTypeFuel (typeCompilationFuel left) left).states)
    (hRetained : source ∉ sequenceDeleted
      (compileTypeFuel (typeCompilationFuel left) left))
    (hComplete : ∀ q ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).futureReachable source,
      ∀ r ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).referencedStates q,
      (∃ residual, (residual, r) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true) →
      ∃ residual, (residual, q) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true) :
    computeFutureOf (.seq alphabet left right) (.child 0 source) =
      computeFutureOf left source ∪
        if ∃ residual, (residual, source) ∈
            buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
            typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true then
          computeFutureOf right (compileTypeFuel (typeCompilationFuel right) right).initial
        else ∅ := by
  have hMenus := compiledMenuFrom_sequence_left alphabet left right hLeftDisjoint hRightDisjoint
    (compiledMenuContribution left) (compiledMenuContribution right)
    (compiledMenuContribution (.seq alphabet left right)) source hSource hRetained hComplete
    (compiledMenuContribution_accepting left)
    (fun q _ hq => compiledMenuContribution_sequence_left alphabet left right q hq)
    (fun q _ => compiledMenuContribution_sequence_right alphabet left right q)
  rw [computeFutureOf_eq_menuFrom, computeFutureOf_eq_menuFrom,
    computeFutureOf_eq_menuFrom]
  rw [hMenus, Finset.filter_union]
  simp only [show (PactType.seq alphabet left right).alphabet = alphabet from rfl,
    hLeftAlphabet, hRightAlphabet]
  split_ifs <;> simp

end

end Pact
