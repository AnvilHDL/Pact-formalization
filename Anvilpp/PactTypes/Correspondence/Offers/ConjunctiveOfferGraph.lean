import Anvilpp.PactTypes.Correspondence.Offers.ExclusiveOfferResolvedEdge

/-!
# buildConjunctiveOfferAutomaton graph structure: entries, offersAt/computeFuture at the root
-/

namespace Pact

noncomputable section

def conjunctiveOfferEntryStates
    (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) :
    Finset TypeAutomatonState :=
  {childState 1 elseAutomaton.initial} ∪
    if branches = [] then ∅ else {childState 0 conjunction.initial}

theorem buildConjunctiveOfferAutomaton_offersAt_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    pending.offersAt .root = typeBranchActions branches := by
  classical
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseAutomaton conjunction
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  ext action
  constructor
  · intro hOffer
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hOffer
    rcases hOffer with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [pending, fragment, buildConjunctiveOfferAutomaton,
      finishAutomatonFragment, Finset.mem_union] at hEdge
    rcases hEdge with ((((hConjunction | hElseChild) | hEnabled) | hWait) |
      hElse)
    · simp only [childPendingEdges, Finset.mem_image] at hConjunction
      rcases hConjunction with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · simp only [childPendingEdges, Finset.mem_image] at hElseChild
      rcases hElseChild with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
      rcases hEnabled with ⟨environment, _, rfl⟩
      simp at hOffer
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _, rfl⟩
      simp only at hSource
      cases hSource
      have hWaiting : action ∈
          (environment.future.image typeNeed) ∩ typeBranchActions branches := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hOffer
      exact (Finset.mem_inter.mp hWaiting).2
    · simp only [Finset.mem_image, Finset.mem_filter] at hElse
      rcases hElse with ⟨environment, _, rfl⟩
      simp only at hSource
      cases hSource
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hOffer
  · intro hAction
    let environment : TypeEnvironment := .empty
    let edge : PendingAutomatonEdge :=
      { source := .root
        environment := environment
        label := .visible TypeLabel.silent
        current := typeBranchActions branches
        future := .at (childState 1 elseAutomaton.initial) ∅
        target := childState 1 elseAutomaton.initial }
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
    · simp only [pending, fragment, buildConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union]
      right
      apply Finset.mem_image.mpr
      refine ⟨environment, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · simp [environment, TypeEnvironment.empty,
          TypeAlphabet.localEnvironments]
      · constructor <;>
          change typeBranchNeeds branches ∩ ∅ = ∅ <;> simp
    · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent,
        hAction]

theorem buildConjunctiveOfferAutomaton_root_references_upper
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    pending.referencedStates .root ⊆
      insert .root
        (conjunctiveOfferEntryStates branches elseAutomaton conjunction) := by
  classical
  dsimp only
  intro target hTarget
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hConjunction | hElseChild) | hEnabled) | hWait) |
    hElse)
  · simp only [childPendingEdges, Finset.mem_image] at hConjunction
    rcases hConjunction with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · simp only [childPendingEdges, Finset.mem_image] at hElseChild
    rcases hElseChild with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
    rcases hEnabled with ⟨environment, hConditions, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = childState 0 conjunction.initial := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    subst target
    have hNonempty : branches ≠ [] := by
      intro hEmpty
      subst branches
      simp [typeBranchNeeds] at hConditions
    simp [conjunctiveOfferEntryStates, hNonempty]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = .root := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    exact Finset.mem_insert.mpr (Or.inl hTarget)
  · simp only [Finset.mem_image, Finset.mem_filter] at hElse
    rcases hElse with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = childState 1 elseAutomaton.initial := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    subst target
    simp [conjunctiveOfferEntryStates]

theorem buildConjunctiveOfferAutomaton_entries_referenced
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (hAvailable : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    conjunctiveOfferEntryStates branches elseAutomaton conjunction ⊆
      pending.referencedStates .root := by
  classical
  dsimp only
  intro target hTarget
  by_cases hEmpty : branches = []
  · subst branches
    simp only [conjunctiveOfferEntryStates, ↓reduceIte, Finset.union_empty,
      Finset.mem_singleton] at hTarget
    subst target
    let environment : TypeEnvironment := .empty
    let edge : PendingAutomatonEdge :=
      { source := .root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 1 elseAutomaton.initial) ∅
        target := childState 1 elseAutomaton.initial }
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
    · simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      right
      apply Finset.mem_image.mpr
      refine ⟨environment, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · simp [environment, TypeEnvironment.empty,
          TypeAlphabet.localEnvironments]
      · simp [typeBranchNeeds, environment, TypeEnvironment.empty]
    · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
  · simp only [conjunctiveOfferEntryStates, hEmpty, if_false,
      Finset.mem_union, Finset.mem_singleton] at hTarget
    rcases hTarget with hElse | hConjunction
    · subst target
      let environment : TypeEnvironment := .empty
      let edge : PendingAutomatonEdge :=
        { source := .root
          environment := environment
          label := .visible TypeLabel.silent
          current := typeBranchActions branches
          future := .at (childState 1 elseAutomaton.initial) ∅
          target := childState 1 elseAutomaton.initial }
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter]
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        right
        apply Finset.mem_image.mpr
        refine ⟨environment, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
        · simp [environment, TypeEnvironment.empty,
            TypeAlphabet.localEnvironments]
        · constructor <;>
            change typeBranchNeeds branches ∩ ∅ = ∅ <;> simp
      · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
    · subst target
      rcases List.exists_cons_of_ne_nil hEmpty with ⟨branch, rest, rfl⟩
      let environment : TypeEnvironment :=
        { immediate := {typeNeed branch.1}, future := ∅, clock := false }
      have hLocal : environment ∈ signature.localEnvironments := by
        simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
          Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
          Finset.mem_image]
        right
        refine ⟨{typeNeed branch.1}, ?_, ∅, by simp, rfl⟩
        simpa using hAvailable branch (by simp)
      have hEnabled : typeBranchNeeds (branch :: rest) ∩
          environment.immediate ≠ ∅ := by
        intro hIntersection
        have hMember : typeNeed branch.1 ∈
            typeBranchNeeds (branch :: rest) ∩ environment.immediate := by
          simp [typeBranchNeeds, environment]
        rw [hIntersection] at hMember
        simp at hMember
      let edge : PendingAutomatonEdge :=
        { source := .root
          environment := environment
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState 0 conjunction.initial) ∅
          target := childState 0 conjunction.initial }
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter]
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [buildConjunctiveOfferAutomaton,
          finishAutomatonFragment, Finset.mem_union]
        left
        left
        right
        exact Finset.mem_image.mpr ⟨environment,
          Finset.mem_filter.mpr ⟨hLocal, hEnabled⟩, rfl⟩
      · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]

private theorem buildConjunctiveOfferAutomaton_computeFuture_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (hAvailable : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions)
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hConjunctionTargets : conjunction.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : conjunction.initial ∈ conjunction.states) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending .root =
      typeBranchActions branches ∪
        (conjunctiveOfferEntryStates branches elseAutomaton conjunction).biUnion
          (computeFuture pending) := by
  classical
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseAutomaton conjunction
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hClosed : pending.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
    exact buildConjunctiveOfferAutomaton_futureTargetsInStates signature
      branches elseAutomaton conjunction hElseTargets hConjunctionTargets
        hElseInitial hConjunctionInitial
  have hRoot : (.root : TypeAutomatonState) ∈ pending.states := by
    simp [pending, fragment, buildConjunctiveOfferAutomaton,
      finishAutomatonFragment]
  have hOffers : pending.offersAt .root = typeBranchActions branches := by
    simpa [pending, fragment] using
      buildConjunctiveOfferAutomaton_offersAt_root signature branches
        elseAutomaton conjunction
  have hUpper : pending.referencedStates .root ⊆ insert .root
      (conjunctiveOfferEntryStates branches elseAutomaton conjunction) := by
    simpa [pending, fragment] using
      buildConjunctiveOfferAutomaton_root_references_upper signature branches
        elseAutomaton conjunction
  have hEntries : conjunctiveOfferEntryStates branches elseAutomaton
      conjunction ⊆ pending.referencedStates .root := by
    simpa [pending, fragment] using
      buildConjunctiveOfferAutomaton_entries_referenced signature branches
        elseAutomaton conjunction hAvailable
  change computeFuture pending .root = typeBranchActions branches ∪
    (conjunctiveOfferEntryStates branches elseAutomaton conjunction).biUnion
      (computeFuture pending)
  rw [computeFuture_eq_offersAt_union_biUnion pending .root
    (conjunctiveOfferEntryStates branches elseAutomaton conjunction) hClosed
      hRoot hUpper hEntries, hOffers]

private theorem buildConjunctiveOfferAutomaton_computeFuture_child
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (index : Nat) (child : AutomatonFragment)
    (hIndex : (index = 0 ∧ child = conjunction) ∨
      (index = 1 ∧ child = elseAutomaton))
    (state : TypeAutomatonState)
    (hTargets : child.FutureTargetsInStates)
    (hState : state ∈ child.states)
    (hCard : child.states.card ≤
      (buildConjunctiveOfferAutomaton signature branches elseAutomaton
        conjunction).states.card) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    computeFuture { states := fragment.states, edges := fragment.edges }
        (childState index state) =
      computeFuture { states := child.states, edges := child.edges } state := by
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseAutomaton conjunction
  apply taggedChild_computeFuture_of_outgoing
    ({ states := fragment.states, edges := fragment.edges } : PendingAutomaton)
    ({ states := child.states, edges := child.edges } : PendingAutomaton) index
  · exact buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseAutomaton conjunction index child hIndex
  · exact PendingAutomaton.referencesClosed_of_futureTargetsInStates child
      hTargets
  · exact hState
  · exact hCard

end

end Pact
