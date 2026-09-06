import Anvilpp.PactTypes.Proofs.Automata.MenuDependenciesLemmas
import Anvilpp.PactTypes.Proofs.Automata.BuildParallelAutomatonLemmas
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MenuMetadata

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

private theorem childPendingEdges_edgeTargetsInStates
    (index : Nat) (fragment : AutomatonFragment)
    (hTargets : fragment.EdgeTargetsInStates) :
    ∀ edge ∈ childPendingEdges index fragment,
      edge.target ∈ childStates index fragment := by
  intro edge hEdge
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  obtain ⟨childEdge, hChildEdge, rfl⟩ := hEdge
  simp [childPendingEdge, childStates, childState,
    hTargets childEdge hChildEdge]

private theorem indexedFragment_edgeTargetsInStates
    (automata : List (BareMessage × AutomatonFragment))
    (hTargets : ∀ entry ∈ automata, entry.2.EdgeTargetsInStates) :
    ∀ edge ∈ indexedFragmentEdges automata,
      edge.target ∈ indexedFragmentStates automata := by
  intro edge hEdge
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChildEdge⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    have hTarget := childPendingEdges_edgeTargetsInStates
      (indexed.2 + 1) indexed.1.2 (hTargets indexed.1 hEntry)
      edge hChildEdge
    rw [indexedFragmentStates, mem_foldl_union_iff]
    exact Or.inr ⟨indexed, hIndexed, hTarget⟩

private theorem buildChoiceAutomaton_edgeTargetsInStates
     (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftTargets : left.EdgeTargetsInStates)
    (hRightTargets : right.EdgeTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    (buildChoiceAutomaton alphabet left right selectionLeft
      selectionRight).EdgeTargetsInStates := by
  intro edge hEdge
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeft | hRight) | hSelection
  · obtain ⟨childEdge, hChildEdge, rfl⟩ := hLeft
    simp [childPendingEdge, buildChoiceAutomaton,
      finishAutomatonFragment, childStates, childState,
      hLeftTargets childEdge hChildEdge]
  · obtain ⟨childEdge, hChildEdge, rfl⟩ := hRight
    simp [childPendingEdge, buildChoiceAutomaton,
      finishAutomatonFragment, childStates, childState,
      hRightTargets childEdge hChildEdge]
  · rcases hSelection with ⟨environment, _, rfl | rfl⟩
    · simp [buildChoiceAutomaton, finishAutomatonFragment,
        childStates, childState, hLeftInitial]
    · simp [buildChoiceAutomaton, finishAutomatonFragment,
        childStates, childState, hRightInitial]

private theorem buildRecursionAutomaton_edgeTargetsInStates
     (alphabet : PactTypeAlphabet)
    (name : String) (body : AutomatonFragment)
    (hBodyTargets : body.EdgeTargetsInStates)
    (hBodyInitial : body.initial ∈ body.states) :
    (buildRecursionAutomaton alphabet name body).EdgeTargetsInStates := by
  intro edge hEdge
  simp only [buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image] at hEdge
  rcases hEdge with ⟨environment, _, rfl⟩ |
      ⟨bodyEdge, hBodyEdge, rfl⟩
  · simp [buildRecursionAutomaton, finishAutomatonFragment,
      childStates, childState, hBodyInitial]
  · by_cases hMarker : bodyEdge.label = .variable name
    · simp [hMarker, buildRecursionAutomaton, finishAutomatonFragment,
        childStates, childState, hBodyInitial]
    · simp [hMarker, buildRecursionAutomaton, finishAutomatonFragment,
        childStates, childState, hBodyTargets bodyEdge hBodyEdge]

private theorem buildSequenceAutomaton_edgeTargetsInStates
     (left right : AutomatonFragment)
    (hLeftTargets : left.EdgeTargetsInStates)
    (hRightTargets : right.EdgeTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    (buildSequenceAutomaton left right).EdgeTargetsInStates := by
  intro edge hEdge
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with (hLeft | hRight) | hRedirect
  · obtain ⟨leftEdge, ⟨hLeftEdge, hNotAccepting⟩, rfl⟩ := hLeft
    simp only [sequenceKeptLeftEdge, buildSequenceAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
      Finset.mem_sdiff]
    exact Or.inl ⟨leftEdge.target,
      ⟨hLeftTargets leftEdge hLeftEdge,
        not_mem_sequenceDeleted_of_not_accepting hNotAccepting.2⟩, rfl⟩
  · obtain ⟨rightEdge, hRightEdge, rfl⟩ := hRight
    simp [childPendingEdge, buildSequenceAutomaton,
      finishAutomatonFragment, childStates, childState,
      hRightTargets rightEdge hRightEdge]
  · obtain ⟨leftEdge, _, rfl⟩ := hRedirect
    simp [sequenceRedirectEdge, buildSequenceAutomaton,
      finishAutomatonFragment, childStates, childState, hRightInitial]

/-- Re-stamping a type with a different boundary alphabet renames no state:
the compiled carrier is the same finite set.  Pairwise disjoint offer-branch
declarations are what keep a conjunctive offer's committed branch in place
when re-stamping erases the annotations that tell two branches apart. -/
theorem compileTypeFuel_states_reannotate
    (fuel : Nat) (processType : PactType)
    (hDisjoint : processType.OfferBranchesDisjoint)
    (alphabet : PactTypeAlphabet) :
    (compileTypeFuel fuel (processType.reannotate alphabet)).states =
      (compileTypeFuel fuel processType).states :=
  (CompiledShape.compileTypeFuel_shapeEq_reannotate fuel processType hDisjoint
    alphabet).1

private theorem buildParallelAutomaton_edgeTargetsInStates

    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hLeftTargets : left.EdgeTargetsInStates)
    (hRightTargets : right.EdgeTargetsInStates)
    (hRestampedLeftTargets :
      ∀ edge ∈ restampedLeft.edges, edge.target ∈ left.states)
    (hRestampedRightTargets :
      ∀ edge ∈ restampedRight.edges, edge.target ∈ right.states) :
    (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
      interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture
      restampedRightFuture).EdgeTargetsInStates := by
  intro edge hEdge
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    parallelRawTransitionEdges, parallelLeftCompleteEdges,
    parallelRightCompleteEdges, parallelLeftCompleteSurvivorEdges,
    parallelRightCompleteSurvivorEdges, parallelLeftCompleteDoneEdges,
    parallelRightCompleteDoneEdges, parallelDoneEdges,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter, Finset.mem_inter] at hEdge
  rcases hEdge with
      ((((((⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, _⟩, rfl⟩ |
        ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, -⟩, rfl⟩) |
        ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, -⟩, rfl⟩) |
        ⟨rightEdge, ⟨hRightEdge, -⟩, rfl⟩) |
        ⟨leftEdge, ⟨hLeftEdge, -⟩, rfl⟩) |
        ⟨rightEdge, ⟨hRightEdge, -⟩, rfl⟩) |
        ⟨leftEdge, ⟨hLeftEdge, -⟩, rfl⟩) |
      ⟨environment, _, rfl⟩
  · by_cases hAccept :
      leftEdge.target ∈ left.accepting ∧ rightEdge.target ∈ right.accepting
    · simp [hAccept, buildParallelAutomaton, finishAutomatonFragment,
        parallelRawTransitionEdges, parallelDoneEdges]
    · simp only [resolveAutomatonEdgesWith, Finset.mem_image]
        at hLeftEdge hRightEdge
      obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
      obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
      have hLeftTargetEq : leftRaw.target = leftEdge.target :=
        congrArg AutomatonFragmentEdge.target hLeftEq
      have hRightTargetEq : rightRaw.target = rightEdge.target :=
        congrArg AutomatonFragmentEdge.target hRightEq
      have hAcceptRaw : ¬(leftRaw.target ∈ left.accepting ∧
          rightRaw.target ∈ right.accepting) := by
        simpa [hLeftTargetEq, hRightTargetEq] using hAccept
      rw [← hLeftEq, ← hRightEq]
      simp only [if_neg hAcceptRaw]
      simp [buildParallelAutomaton, finishAutomatonFragment,
        parallelRawTransitionEdges, parallelDoneEdges,
        hLeftTargets leftRaw hLeftRaw,
        hRightTargets rightRaw hRightRaw]
  · simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightEdge
    obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
    rw [← hRightEq]
    simp [buildParallelAutomaton, finishAutomatonFragment,
      parallelRawTransitionEdges, parallelLeftCompleteEdges,
      parallelRightCompleteEdges, parallelDoneEdges,
      hRightTargets rightRaw hRightRaw]
  · simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
    obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
    rw [← hLeftEq]
    simp [buildParallelAutomaton, finishAutomatonFragment,
      parallelRawTransitionEdges, parallelLeftCompleteEdges,
      parallelRightCompleteEdges, parallelDoneEdges,
      hLeftTargets leftRaw hLeftRaw]

  · simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightEdge
    obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
    rw [← hRightEq]
    simp [buildParallelAutomaton, finishAutomatonFragment,
      parallelRawTransitionEdges, parallelLeftCompleteEdges,
      parallelRightCompleteEdges, parallelDoneEdges,
      hRestampedRightTargets rightRaw hRightRaw]
  · simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
    obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
    rw [← hLeftEq]
    simp [buildParallelAutomaton, finishAutomatonFragment,
      parallelRawTransitionEdges, parallelLeftCompleteEdges,
      parallelRightCompleteEdges, parallelDoneEdges,
      hRestampedLeftTargets leftRaw hLeftRaw]
  · simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightEdge
    obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
    rw [← hRightEq]
    simp [buildParallelAutomaton, finishAutomatonFragment]
  · simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
    obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
    rw [← hLeftEq]
    simp [buildParallelAutomaton, finishAutomatonFragment]
  · simp [buildParallelAutomaton, finishAutomatonFragment,
      parallelRawTransitionEdges, parallelLeftCompleteEdges,
      parallelRightCompleteEdges, parallelDoneEdges]


private theorem buildExclusiveOfferAutomaton_edgeTargetsInStates
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.EdgeTargetsInStates)
    (hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.EdgeTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states) :
    (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
      branchAutomata).EdgeTargetsInStates := by
  intro edge hEdge
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
  · have hTarget := childPendingEdges_edgeTargetsInStates 0 elseAutomaton
      hElseTargets edge hElse
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_edgeTargetsInStates branchAutomata
      hBranchTargets edge hIndexed
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
    · simp at hEmpty
    · have hEntry : indexed.1 ∈ branchAutomata := by
        have hMapped : indexed.1 ∈ branchAutomata.zipIdx.map Prod.fst :=
          List.mem_map_of_mem (f := Prod.fst) hIndexed
        simpa using hMapped
      simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, _, rfl⟩ := hNewEdge
      have hIndexedState : childState (indexed.2 + 1)
          indexed.1.2.initial ∈ indexedFragmentStates branchAutomata := by
        rw [indexedFragmentStates, mem_foldl_union_iff]
        exact Or.inr ⟨indexed, hIndexed, by
          simp [childStates, childState, hBranchInitial indexed.1 hEntry]⟩
      simp [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        hIndexedState]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, _, rfl⟩ := hWait
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, _, rfl⟩ := hResolved
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

private theorem buildSelectedConjunctiveOfferAutomaton_edgeTargetsInStates
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.EdgeTargetsInStates)
    (hConjunctionTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.EdgeTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states) :
    (buildSelectedConjunctiveOfferAutomaton alphabet branches
      elseAutomaton selectedConjunctions).EdgeTargetsInStates := by
  intro edge hEdge
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hConjunction) | hEnabled) | hWait) | hResolved)
  · have hTarget := childPendingEdges_edgeTargetsInStates 0 elseAutomaton
      hElseTargets edge hElse
    simp [buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_edgeTargetsInStates
      selectedConjunctions hConjunctionTargets edge hConjunction
    simp [buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment, hTarget]
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
    · simp at hEmpty
    · have hEntry : indexed.1 ∈ selectedConjunctions := by
        have hMapped : indexed.1 ∈ selectedConjunctions.zipIdx.map Prod.fst :=
          List.mem_map_of_mem (f := Prod.fst) hIndexed
        simpa using hMapped
      simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, _, rfl⟩ := hNewEdge
      have hIndexedState : childState (indexed.2 + 1)
          indexed.1.2.initial ∈
            indexedFragmentStates selectedConjunctions := by
        rw [indexedFragmentStates, mem_foldl_union_iff]
        exact Or.inr ⟨indexed, hIndexed, by
          simp [childStates, childState,
            hConjunctionInitial indexed.1 hEntry]⟩
      simp [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, hIndexedState]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, _, rfl⟩ := hWait
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, _, rfl⟩ := hResolved
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/-- Every edge emitted by a sufficiently fuelled compilation targets a state
declared by that same compiled fragment. -/
theorem compileTypeFuel_edgeTargetsInStates  :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      processType.OfferBranchesDisjoint →
      (compileTypeFuel fuel processType).EdgeTargetsInStates := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel _
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel hDisjoint
      cases processType with
      | message _ msg dir =>
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image] at hEdge
          rcases hEdge with
            (⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩) |
              ⟨environment, _, rfl⟩ <;>
            simp [compileTypeFuel, finishAutomatonFragment]
      | progress _ pid =>
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ |
            ⟨environment, _, rfl⟩ <;>
            simp [compileTypeFuel, finishAutomatonFragment]
      | tock _ =>
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ |
            ⟨environment, _, rfl⟩
          · by_cases hClock : environment.clock <;>
              simp [hClock, compileTypeFuel, finishAutomatonFragment]
          · simp [compileTypeFuel, finishAutomatonFragment]
      | skip _ =>
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image] at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp [compileTypeFuel, finishAutomatonFragment]
      | var _ name =>
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image] at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp [compileTypeFuel, finishAutomatonFragment]
      | recur _ name body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          exact buildRecursionAutomaton_edgeTargetsInStates _ name
            (compileTypeFuel fuel body) (ih body hBody hDisjoint)
            (compileTypeFuel_initial_mem fuel body hBody)
      | choice _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_edgeTargetsInStates _
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right) .silent .silent
            (ih left hLeft hDisjoint.1) (ih right hRight hDisjoint.2)
            (compileTypeFuel_initial_mem fuel left hLeft)
            (compileTypeFuel_initial_mem fuel right hRight)
      | fairChoice _ bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_edgeTargetsInStates _
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right) (.fair bid true)
            (.fair bid false) (ih left hLeft hDisjoint.1)
            (ih right hRight hDisjoint.2)
            (compileTypeFuel_initial_mem fuel left hLeft)
            (compileTypeFuel_initial_mem fuel right hRight)
      | seq _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          exact buildSequenceAutomaton_edgeTargetsInStates
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right) (ih left hLeft hDisjoint.1)
            (ih right hRight hDisjoint.2)
            (compileTypeFuel_initial_mem fuel right hRight)
      | par alphabet left right interface =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          have hLeftRestamped :
              TypeCompilationFuelSufficient (left.reannotate alphabet) fuel := by
            show typeCompilationFuel (left.reannotate alphabet) ≤ fuel
            rw [typeCompilationFuel_reannotate]; exact hLeft
          have hRightRestamped :
              TypeCompilationFuelSufficient (right.reannotate alphabet) fuel := by
            show typeCompilationFuel (right.reannotate alphabet) ≤ fuel
            rw [typeCompilationFuel_reannotate]; exact hRight
          exact buildParallelAutomaton_edgeTargetsInStates alphabet
            left.alphabet right.alphabet interface
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right)
            (compileTypeFuel fuel (left.reannotate alphabet))
            (compileTypeFuel fuel (right.reannotate alphabet))
            (compiledChildFutureFuel fuel left)
            (compiledChildFutureFuel fuel right)
            (computeFutureOfFuel (min fuel (typeCompilationFuel left))
              (left.reannotate alphabet))
            (computeFutureOfFuel (min fuel (typeCompilationFuel right))
              (right.reannotate alphabet))
            (ih left hLeft hDisjoint.1) (ih right hRight hDisjoint.2)
            (fun edge hEdge => by
              rw [← compileTypeFuel_states_reannotate fuel left hDisjoint.1
                alphabet]
              exact ih (left.reannotate alphabet) hLeftRestamped
                (reannotate_offerBranchesDisjoint left alphabet hDisjoint.1)
                edge hEdge)
            (fun edge hEdge => by
              rw [← compileTypeFuel_states_reannotate fuel right hDisjoint.2
                alphabet]
              exact ih (right.reannotate alphabet) hRightRestamped
                (reannotate_offerBranchesDisjoint right alphabet hDisjoint.2)
                edge hEdge)
      | xoffer _ elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hBranches : ∀ entry ∈ branches,
              TypeCompilationFuelSufficient entry.2 fuel := by
            intro entry hEntry
            have hBound := typeCompilationFuel_le_typeBranchCompilationFuel
              branches entry hEntry
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            simp only [TypeCompilationFuelSufficient]
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          apply buildExclusiveOfferAutomaton_edgeTargetsInStates
          · exact ih elseType hElse hDisjoint.1
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact ih original.2 (hBranches original hOriginal)
              (offerBranchesDisjoint_of_mem_branch hDisjoint.2 hOriginal)
          · exact compileTypeFuel_initial_mem fuel elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact compileTypeFuel_initial_mem fuel original.2
              (hBranches original hOriginal)
      | offer alphabet elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hSelected : ∀ selected ∈ branches,
              TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting alphabet selected branches) fuel := by
            intro selected hSelected
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          apply buildSelectedConjunctiveOfferAutomaton_edgeTargetsInStates
          · exact ih elseType hElse hDisjoint.1
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact ih (parallelTypeBranchesSelecting alphabet original branches)
              (hSelected original hOriginal)
              (parallelTypeBranchesSelecting_offerBranchesDisjoint original
                branches fun item hItem =>
                  offerBranchesDisjoint_of_mem_branch hDisjoint.2.2 hItem)
          · exact compileTypeFuel_initial_mem fuel elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact compileTypeFuel_initial_mem fuel
              (parallelTypeBranchesSelecting alphabet original branches)
              (hSelected original hOriginal)

/-- In a clock environment only the clock itself can fire, with no offers.

The automaton-side mirror of `typeOffers_label_eq_tock_of_clock` and
`typeOffers_current_empty_of_clock`.  Every edge family either carries an
explicit `clock = false` guard, or fires an action needing a non-empty
immediate need that a clocked environment cannot supply; only `.tock`'s own
fire edge is tock-labelled, and it has empty offers. -/
theorem compileTypeFuel_clockEdgesAreTock  :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      (compileTypeFuel fuel processType).ClockEdgesAreTock := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message _ msg dir =>
          intro edge hEdge hClock
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with
            (⟨environment, ⟨hEnvMem, hNeed⟩, rfl⟩ |
              ⟨environment, ⟨_, hNotClock, _⟩, rfl⟩) |
              ⟨environment, ⟨_, hNotClock⟩, rfl⟩
          · -- Firing needs an immediate need; a clocked environment has none.
            exfalso
            simp only at hClock
            rw [TypeEnvironment.hasNeed,
              PactTypeAlphabet.immediate_eq_empty_of_mem_localEnvironments_of_clock
                hEnvMem hClock] at hNeed
            exact absurd hNeed (by simp)
          · exfalso
            simp only at hClock
            rw [hNotClock] at hClock
            exact absurd hClock (by simp)
          · exfalso
            simp only at hClock
            rw [hNotClock] at hClock
            exact absurd hClock (by simp)
      | progress _ pid =>
          intro edge hEdge hClock
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, ⟨_, hNotClock⟩, rfl⟩ |
            ⟨environment, ⟨_, hNotClock⟩, rfl⟩ <;>
            · exfalso
              simp only at hClock
              rw [hNotClock] at hClock
              exact absurd hClock (by simp)
      | tock _ =>
          intro edge hEdge hClock
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ |
            ⟨environment, ⟨_, hNotClock⟩, rfl⟩
          · -- The clock's own fire edge: tock-labelled with empty offers.
            by_cases hEnvClock : environment.clock
            · rw [if_pos hEnvClock]
              exact ⟨rfl, rfl⟩
            · exfalso
              rw [if_neg hEnvClock] at hClock
              simp only at hClock
              simp only [Bool.not_eq_true] at hEnvClock
              rw [hEnvClock] at hClock
              exact absurd hClock (by simp)
          · exfalso
            simp only at hClock
            rw [hNotClock] at hClock
            exact absurd hClock (by simp)
      | skip _ =>
          intro edge hEdge hClock
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          obtain ⟨environment, ⟨_, hNotClock⟩, rfl⟩ := hEdge
          exfalso
          simp only at hClock
          rw [hNotClock] at hClock
          exact absurd hClock (by simp)
      | var _ name =>
          -- Marker edges are now guarded on `clock = false`, so a clocked
          -- marker (whose semantic label is `silent`, not `tock`) cannot
          -- arise.  This guard is what makes the `recur` case below work.
          intro edge hEdge hClock
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          obtain ⟨environment, ⟨_, hNotClock⟩, rfl⟩ := hEdge
          exfalso
          simp only at hClock
          rw [hNotClock] at hClock
          exact absurd hClock (by simp)
      | recur _ name body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildRecursionAutomaton_clockEdgesAreTock _ name
            (compileTypeFuel fuel body) (ih body hBody)
      | choice _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_clockEdgesAreTock _
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right) .silent .silent
            (ih left hLeft) (ih right hRight)
      | fairChoice _ bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_clockEdgesAreTock _
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right) (.fair bid true)
            (.fair bid false) (ih left hLeft) (ih right hRight)
      | seq _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildSequenceAutomaton_clockEdgesAreTock
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right) (ih left hLeft)
            (ih right hRight)
      | par alphabet left right interface =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          have hLeftRestamped :
              TypeCompilationFuelSufficient (left.reannotate alphabet) fuel := by
            show typeCompilationFuel (left.reannotate alphabet) ≤ fuel
            rw [typeCompilationFuel_reannotate]; exact hLeft
          have hRightRestamped :
              TypeCompilationFuelSufficient (right.reannotate alphabet) fuel := by
            show typeCompilationFuel (right.reannotate alphabet) ≤ fuel
            rw [typeCompilationFuel_reannotate]; exact hRight
          exact buildParallelAutomaton_clockEdgesAreTock alphabet
            left.alphabet right.alphabet interface
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right)
            (compileTypeFuel fuel (left.reannotate alphabet))
            (compileTypeFuel fuel (right.reannotate alphabet))
            (compiledChildFutureFuel fuel left)
            (compiledChildFutureFuel fuel right)
            (computeFutureOfFuel (min fuel (typeCompilationFuel left))
              (left.reannotate alphabet))
            (computeFutureOfFuel (min fuel (typeCompilationFuel right))
              (right.reannotate alphabet))
            (ih left hLeft) (ih right hRight)
            (ih (left.reannotate alphabet) hLeftRestamped)
            (ih (right.reannotate alphabet) hRightRestamped)
      | xoffer _ elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hBranches : ∀ entry ∈ branches,
              TypeCompilationFuelSufficient entry.2 fuel := by
            intro entry hEntry
            have hBound := typeCompilationFuel_le_typeBranchCompilationFuel
              branches entry hEntry
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            simp only [TypeCompilationFuelSufficient]
            omega
          rw [compileTypeFuel.eq_def]
          apply buildExclusiveOfferAutomaton_clockEdgesAreTock
          · exact ih elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact ih original.2 (hBranches original hOriginal)
      | offer alphabet elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hSelected : ∀ selected ∈ branches,
              TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting alphabet selected branches) fuel := by
            intro selected hSelected
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          rw [compileTypeFuel.eq_def]
          apply buildSelectedConjunctiveOfferAutomaton_clockEdgesAreTock
          · exact ih elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact ih (parallelTypeBranchesSelecting alphabet original branches)
              (hSelected original hOriginal)

theorem compileTypeFuel_futureTargetsInStates  :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      processType.OfferBranchesDisjoint →
      (compileTypeFuel fuel processType).FutureTargetsInStates := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel _
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel hDisjoint
      cases processType with
      | message _ msg dir =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image] at hEdge
          rcases hEdge with
            (⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩) |
              ⟨environment, _, rfl⟩ <;>
            simp at hFuture <;>
            rcases hFuture with ⟨rfl, rfl⟩ <;>
            simp [compileTypeFuel, finishAutomatonFragment]

      | progress _ pid =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩ <;>
            simp at hFuture <;>
            rcases hFuture with ⟨rfl, rfl⟩ <;>
            simp [compileTypeFuel, finishAutomatonFragment]
      | tock _ =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩
          · split at hFuture <;> simp at hFuture <;>
              rcases hFuture with ⟨rfl, rfl⟩ <;>
              simp [compileTypeFuel, finishAutomatonFragment]
          · simp at hFuture
            rcases hFuture with ⟨rfl, rfl⟩
            simp [compileTypeFuel, finishAutomatonFragment]
      | skip _ =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image]
            at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp at hFuture
          rcases hFuture with ⟨rfl, rfl⟩
          simp [compileTypeFuel, finishAutomatonFragment]
      | var _ name =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image]
            at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp at hFuture
          rcases hFuture with ⟨rfl, rfl⟩
          simp [compileTypeFuel, finishAutomatonFragment]
      | recur _ name body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          exact buildRecursionAutomaton_futureTargetsInStates _ name
            (compileTypeFuel fuel body) (ih body hBody hDisjoint)
            (compileTypeFuel_initial_mem fuel body hBody)
      | choice _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_futureTargetsInStates _
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right) TypeLabel.silent
            TypeLabel.silent (ih left hLeft hDisjoint.1)
            (ih right hRight hDisjoint.2)
            (compileTypeFuel_initial_mem fuel left hLeft)
            (compileTypeFuel_initial_mem fuel right hRight)
      | fairChoice _ bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_futureTargetsInStates _
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right) (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) (ih left hLeft hDisjoint.1)
            (ih right hRight hDisjoint.2)
            (compileTypeFuel_initial_mem fuel left hLeft)
            (compileTypeFuel_initial_mem fuel right hRight)
      | seq _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          exact buildSequenceAutomaton_futureTargetsInStates
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right) (ih right hRight hDisjoint.2)
            (compileTypeFuel_edgeTargetsInStates fuel left hLeft hDisjoint.1)
            (compileTypeFuel_initial_mem fuel right hRight)
      | par alphabet left right interface =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          have hLeftRestamped :
              TypeCompilationFuelSufficient (left.reannotate alphabet) fuel := by
            show typeCompilationFuel (left.reannotate alphabet) ≤ fuel
            rw [typeCompilationFuel_reannotate]; exact hLeft
          have hRightRestamped :
              TypeCompilationFuelSufficient (right.reannotate alphabet) fuel := by
            show typeCompilationFuel (right.reannotate alphabet) ≤ fuel
            rw [typeCompilationFuel_reannotate]; exact hRight
          exact buildParallelAutomaton_futureTargetsInStates alphabet
            left.alphabet right.alphabet interface
            (compileTypeFuel fuel left)
            (compileTypeFuel fuel right)
            (compileTypeFuel fuel (left.reannotate alphabet))
            (compileTypeFuel fuel (right.reannotate alphabet))
            (compiledChildFutureFuel fuel left)
            (compiledChildFutureFuel fuel right)
            (computeFutureOfFuel (min fuel (typeCompilationFuel left))
              (left.reannotate alphabet))
            (computeFutureOfFuel (min fuel (typeCompilationFuel right))
              (right.reannotate alphabet))
            (compileTypeFuel_edgeTargetsInStates fuel left hLeft hDisjoint.1)
            (compileTypeFuel_edgeTargetsInStates fuel right hRight
              hDisjoint.2)
            (fun edge hEdge => by
              rw [← compileTypeFuel_states_reannotate fuel left hDisjoint.1
                alphabet]
              exact compileTypeFuel_edgeTargetsInStates fuel
                (left.reannotate alphabet) hLeftRestamped
                (reannotate_offerBranchesDisjoint left alphabet hDisjoint.1)
                edge hEdge)
            (fun edge hEdge => by
              rw [← compileTypeFuel_states_reannotate fuel right hDisjoint.2
                alphabet]
              exact compileTypeFuel_edgeTargetsInStates fuel
                (right.reannotate alphabet) hRightRestamped
                (reannotate_offerBranchesDisjoint right alphabet hDisjoint.2)
                edge hEdge)
      | xoffer alphabet elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hBranches : ∀ entry ∈ branches,
              TypeCompilationFuelSufficient entry.2 fuel := by
            intro entry hEntry
            have hBound := typeCompilationFuel_le_typeBranchCompilationFuel
              branches entry hEntry
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            simp only [TypeCompilationFuelSufficient]
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          have hResult := buildExclusiveOfferAutomaton_futureTargetsInStates
            alphabet branches (compileTypeFuel fuel elseType)
            (branches.map fun branch =>
              (branch.1, compileTypeFuel fuel branch.2))
            (ih elseType hElse hDisjoint.1)
            (by
              intro entry hEntry
              simp only [List.mem_map] at hEntry
              obtain ⟨original, hOriginal, rfl⟩ := hEntry
              exact ih original.2 (hBranches original hOriginal)
                (offerBranchesDisjoint_of_mem_branch hDisjoint.2 hOriginal))
            (compileTypeFuel_initial_mem fuel elseType hElse)
            (by
              intro entry hEntry
              simp only [List.mem_map] at hEntry
              obtain ⟨original, hOriginal, rfl⟩ := hEntry
              exact compileTypeFuel_initial_mem fuel original.2
                (hBranches original hOriginal))
          simpa [compileTypeFuel] using hResult
      | offer alphabet elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hSelected : ∀ selected ∈ branches,
              TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting alphabet selected branches) fuel := by
            intro selected hSelected
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rw [compileTypeFuel.eq_def]
          have hResult :=
            buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates
              alphabet branches
              (compileTypeFuel fuel elseType)
              (branches.map fun selected =>
                (selected.1, compileTypeFuel fuel
                  (parallelTypeBranchesSelecting alphabet selected branches)))
              (ih elseType hElse hDisjoint.1)
              (by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨original, hOriginal, rfl⟩ := hEntry
                exact ih (parallelTypeBranchesSelecting alphabet original branches)
                  (hSelected original hOriginal)
                  (parallelTypeBranchesSelecting_offerBranchesDisjoint original
                    branches fun item hItem =>
                      offerBranchesDisjoint_of_mem_branch hDisjoint.2.2 hItem))
              (compileTypeFuel_initial_mem fuel elseType hElse)
              (by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨original, hOriginal, rfl⟩ := hEntry
                exact compileTypeFuel_initial_mem fuel
                  (parallelTypeBranchesSelecting alphabet original branches)
                  (hSelected original hOriginal))
          simpa [compileTypeFuel] using hResult

/-- Proves every sufficiently fuelled fragment's pending automaton is closed under its own future references. -/
theorem compileTypeFuel_referencesClosed
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hDisjoint : processType.OfferBranchesDisjoint) :
    ({ states := (compileTypeFuel fuel processType).states
       edges := (compileTypeFuel fuel processType).edges } :
      PendingAutomaton).ReferencesClosed :=
  PendingAutomaton.referencesClosed_of_futureTargetsInStates
    (compileTypeFuel fuel processType)
    (compileTypeFuel_futureTargetsInStates fuel processType hFuel hDisjoint)

/-- Both execution references and menu-only dependencies stay in the carrier. -/
theorem compiledMenuGraphFuel_referencesClosed
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hDisjoint : processType.OfferBranchesDisjoint) :
    (compiledMenuGraphFuel fuel processType).ReferencesClosed := by
  unfold compiledMenuGraphFuel
  apply PendingAutomaton.referencesClosed_withMenuDependencies
  · exact compileTypeFuel_referencesClosed fuel processType hFuel hDisjoint
  · intro link hLink
    simp only [Nat.min_eq_right hFuel] at hLink
    rw [compileTypeFuel_eq_of_sufficient processType hFuel le_rfl]
    exact compileTypeMenuLinksFuel_targets_mem (typeCompilationFuel processType)
      processType le_rfl hDisjoint link hLink

private theorem stateProductInfoFuel_succ_stable :
    ∀ fuel processType state,
      typeCompilationFuel processType ≤ fuel →
      stateProductInfoFuel (fuel + 1) processType state =
        stateProductInfoFuel fuel processType state := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType state hFuel
      have hPositive := typeCompilationFuel_positive processType
      omega
  | succ fuel ih =>
      intro processType state hFuel
      cases processType with
      | message _ msg dir => cases state <;> rfl
      | progress _ pid => cases state <;> rfl
      | tock _ => cases state <;> rfl
      | skip _ => cases state <;> rfl
      | var _ name => cases state <;> rfl
      | recur _ name body =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ index =>
                  cases index <;> rfl
          | _ => rfl
      | choice _ left right =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ index =>
                  cases index with
                  | zero =>
                      simp only [stateProductInfoFuel]
                      apply ih
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
                  | succ index => rfl
          | _ => rfl
      | fairChoice _ bid left right =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ index =>
                  cases index with
                  | zero =>
                      simp only [stateProductInfoFuel]
                      apply ih
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
                  | succ index => rfl
          | _ => rfl
      | seq _ left right =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ index =>
                  cases index with
                  | zero =>
                      simp only [stateProductInfoFuel]
                      apply ih
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
                  | succ index => rfl
          | _ => rfl
      | par alphabet left right interface =>
          cases state with
          | survivor index q =>
              cases index with
              | zero =>
                  have hLeft :
                      typeCompilationFuel (left.reannotate alphabet) ≤ fuel := by
                    rw [typeCompilationFuel_reannotate]
                    simp [typeCompilationFuel] at hFuel; omega
                  simp only [stateProductInfoFuel]
                  exact ih (left.reannotate alphabet) q hLeft
              | succ index =>
                  cases index with
                  | zero =>
                      have hRight :
                          typeCompilationFuel (right.reannotate alphabet) ≤
                            fuel := by
                        rw [typeCompilationFuel_reannotate]
                        simp [typeCompilationFuel] at hFuel; omega
                      simp only [stateProductInfoFuel]
                      exact ih (right.reannotate alphabet) q hRight
                  | succ index => rfl
          | _ => rfl
      | xoffer _ elseType branches =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ i =>
                  simp only [stateProductInfoFuel]
                  cases hBranch : branches[i]? with
                  | none => rfl
                  | some branch =>
                      rcases branch with ⟨action, branchType⟩
                      apply ih
                      have hMem : (action, branchType) ∈ branches :=
                        List.mem_iff_getElem?.mpr ⟨i, hBranch⟩
                      have hBranchFuel :=
                        typeCompilationFuel_le_typeBranchCompilationFuel
                          branches (action, branchType) hMem
                      have hBranchFuel' :
                          typeCompilationFuel branchType ≤
                            typeBranchCompilationFuel branches := by
                        simpa using hBranchFuel
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
          | _ => rfl
      | offer _ elseType branches =>
          cases state with
          | child index q =>
              cases index with
              | zero =>
                  simp only [stateProductInfoFuel]
                  apply ih
                  simp [typeCompilationFuel] at hFuel ⊢
                  omega
              | succ i =>
                  simp only [stateProductInfoFuel]
                  cases hSelected : branches[i]? with
                  | none => rfl
                  | some selected =>
                      apply ih
                      rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                      simp [typeCompilationFuel] at hFuel ⊢
                      omega
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
        stateProductInfoFuel_succ_stable (fuel + extra) processType state
          (by omega),
        ih]

/-- States that `stateProductInfoFuel` stabilizes once its fuel is sufficient, mirroring `compileTypeFuel_eq_of_sufficient`. -/
theorem stateProductInfoFuel_eq_of_sufficient
    (processType : PactType) (state : TypeAutomatonState)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    stateProductInfoFuel leftFuel processType state =
      stateProductInfoFuel rightFuel processType state := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (stateProductInfoFuel_add_stable processType state leftFuel extra
      hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact stateProductInfoFuel_add_stable processType state rightFuel extra
      hRight

theorem stateProductInfoFuel_component_fuel_lt :
    ∀ fuel processType state interface left right q1 q2,
      TypeCompilationFuelSufficient processType fuel →
      stateProductInfoFuel fuel processType state =
        some (interface, left, right, q1, q2) →
      typeCompilationFuel left < fuel ∧
        typeCompilationFuel right < fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType state interface left right q1 q2 hFuel _hInfo
      have hPositive := typeCompilationFuel_positive processType
      exact (by
        simp [TypeCompilationFuelSufficient] at hFuel
        omega)
  | succ fuel ih =>
      intro processType state interface componentLeft componentRight q1 q2
        hFuel hInfo
      cases processType with
      | message _ msg dir => cases state <;> simp [stateProductInfoFuel] at hInfo
      | progress _ pid => cases state <;> simp [stateProductInfoFuel] at hInfo
      | tock _ => cases state <;> simp [stateProductInfoFuel] at hInfo
      | skip _ => cases state <;> simp [stateProductInfoFuel] at hInfo
      | var _ name => cases state <;> simp [stateProductInfoFuel] at hInfo
      | recur _ name body =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih body state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ index =>
                  cases index <;> simp [stateProductInfoFuel] at hInfo
          | _ => simp [stateProductInfoFuel] at hInfo
      | choice _ left right =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih left state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ index =>
                  cases index with
                  | zero =>
                      obtain ⟨hLeft, hRight⟩ :=
                        ih right state interface componentLeft componentRight q1 q2
                          (by
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [stateProductInfoFuel] using hInfo)
                      constructor <;> omega
                  | succ index => simp [stateProductInfoFuel] at hInfo
          | _ => simp [stateProductInfoFuel] at hInfo
      | fairChoice _ bid left right =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih left state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ index =>
                  cases index with
                  | zero =>
                      obtain ⟨hLeft, hRight⟩ :=
                        ih right state interface componentLeft componentRight q1 q2
                          (by
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [stateProductInfoFuel] using hInfo)
                      constructor <;> omega
                  | succ index => simp [stateProductInfoFuel] at hInfo
          | _ => simp [stateProductInfoFuel] at hInfo
      | seq _ left right =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih left state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ index =>
                  cases index with
                  | zero =>
                      obtain ⟨hLeft, hRight⟩ :=
                        ih right state interface componentLeft componentRight q1 q2
                          (by
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [stateProductInfoFuel] using hInfo)
                      constructor <;> omega
                  | succ index => simp [stateProductInfoFuel] at hInfo
          | _ => simp [stateProductInfoFuel] at hInfo
      | par alphabet left right productInterface =>
          cases state with
          | pair leftState rightState =>
              simp only [stateProductInfoFuel, Option.some.injEq,
                Prod.mk.injEq] at hInfo
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hInfo
              simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
              constructor <;> omega
          | survivor index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeftLt, hRightLt⟩ :=
                    ih (left.reannotate alphabet) state interface
                      componentLeft componentRight q1 q2
                      (by
                        show typeCompilationFuel (left.reannotate alphabet) ≤ fuel
                        rw [typeCompilationFuel_reannotate]
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ index =>
                  cases index with
                  | zero =>
                      obtain ⟨hLeftLt, hRightLt⟩ :=
                        ih (right.reannotate alphabet) state interface
                          componentLeft componentRight q1 q2
                          (by
                            show typeCompilationFuel (right.reannotate alphabet)
                              ≤ fuel
                            rw [typeCompilationFuel_reannotate]
                            simp [TypeCompilationFuelSufficient,
                              typeCompilationFuel] at hFuel
                            omega)
                          (by simpa [stateProductInfoFuel] using hInfo)
                      constructor <;> omega
                  | succ index => simp [stateProductInfoFuel] at hInfo
          | _ => simp [stateProductInfoFuel] at hInfo
      | xoffer _ elseType branches =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih elseType state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ i =>
                  simp only [stateProductInfoFuel] at hInfo
                  cases hBranch : branches[i]? with
                  | none => simp [hBranch] at hInfo
                  | some branch =>
                      rcases branch with ⟨action, branchType⟩
                      obtain ⟨hLeft, hRight⟩ :=
                        ih branchType state interface componentLeft componentRight q1 q2
                          (by
                            have hMem : (action, branchType) ∈ branches :=
                              List.mem_iff_getElem?.mpr ⟨i, hBranch⟩
                            have hBranchFuel :=
                              typeCompilationFuel_le_typeBranchCompilationFuel branches
                                (action, branchType) hMem
                            have hBranchFuel' :
                                typeCompilationFuel branchType ≤
                                  typeBranchCompilationFuel branches := by
                              simpa using hBranchFuel
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [hBranch] using hInfo)
                      constructor <;> omega
          | _ => simp [stateProductInfoFuel] at hInfo
      | offer alphabet elseType branches =>
          cases state with
          | child index state =>
              cases index with
              | zero =>
                  obtain ⟨hLeft, hRight⟩ :=
                    ih elseType state interface componentLeft componentRight q1 q2
                      (by
                        simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                          at hFuel ⊢
                        omega)
                      (by simpa [stateProductInfoFuel] using hInfo)
                  constructor <;> omega
              | succ i =>
                  simp only [stateProductInfoFuel] at hInfo
                  cases hSelected : branches[i]? with
                  | none => simp [hSelected] at hInfo
                  | some selected =>
                      obtain ⟨hLeft, hRight⟩ :=
                        ih (parallelTypeBranchesSelecting alphabet selected branches) state
                          interface componentLeft componentRight q1 q2
                          (by
                            unfold TypeCompilationFuelSufficient
                            rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                              at hFuel ⊢
                            omega)
                          (by simpa [hSelected] using hInfo)
                      constructor <;> omega
          | _ => simp [stateProductInfoFuel] at hInfo

private theorem computeFutureOfFuel_succ_stable :
    ∀ fuel processType state,
      TypeCompilationFuelSufficient processType fuel →
      computeFutureOfFuel (fuel + 1) processType state =
        computeFutureOfFuel fuel processType state := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType state hFuel
      have hPositive := typeCompilationFuel_positive processType
      simp [TypeCompilationFuelSufficient] at hFuel
      omega
  | succ fuel ih =>
      intro processType state hFuel
      conv_lhs => rw [computeFutureOfFuel]
      conv_rhs => rw [computeFutureOfFuel]
      have hCompile :
          compileTypeFuel (fuel + 1 + 1) processType =
            compileTypeFuel (fuel + 1) processType :=
        compileTypeFuel_eq_of_sufficient processType
          (by
            simp only [TypeCompilationFuelSufficient] at hFuel ⊢
            omega)
          hFuel
      rw [hCompile]
      simp only [Nat.min_eq_right hFuel, Nat.min_eq_right (Nat.le.step hFuel)]
      -- Both sides carry the same alphabet gate, so it is enough to match
      -- the sets it filters.
      refine congrArg (Finset.filter _) ?_
      apply Finset.biUnion_congr rfl
      intro visited _hVisited
      cases hInfo : stateProductInfo processType visited with
      | none => simp
      | some info =>
          rcases info with ⟨interface, left, right, q1, q2⟩
          have hInfoFuel :
              stateProductInfoFuel (typeCompilationFuel processType)
                  processType visited = some (interface, left, right, q1, q2) := by
            simpa [stateProductInfo] using hInfo
          obtain ⟨hLeftLt, hRightLt⟩ :=
            stateProductInfoFuel_component_fuel_lt
              (typeCompilationFuel processType) processType visited interface
              left right q1 q2 (typeCompilationFuel_sufficient processType)
              hInfoFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient] at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient] at hFuel ⊢
            omega
          simp only
          rw [ih left q1 hLeftFuel, ih right q2 hRightFuel]

private theorem computeFutureOfFuel_add_stable
     (processType : PactType)
    (state : TypeAutomatonState) (fuel extra : Nat)
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    computeFutureOfFuel (fuel + extra) processType state =
      computeFutureOfFuel fuel processType state := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        computeFutureOfFuel_succ_stable (fuel + extra) processType state
          (by
            simp [TypeCompilationFuelSufficient] at hFuel ⊢
            omega),
        ih]

/-- States that `computeFutureOfFuel` stabilizes once its fuel is sufficient, mirroring `compileTypeFuel_eq_of_sufficient`. -/
theorem computeFutureOfFuel_eq_of_sufficient
     (processType : PactType) (state : TypeAutomatonState)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    computeFutureOfFuel leftFuel processType state =
      computeFutureOfFuel rightFuel processType state := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (computeFutureOfFuel_add_stable processType state leftFuel
      extra hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact computeFutureOfFuel_add_stable processType state rightFuel
      extra hRight

private theorem offersAt_of_outgoing_childPendingEdge
    (parent child : AutomatonFragment) (index : Nat)
    (state : TypeAutomatonState)
    (hOutgoing : ∀ edge : PendingAutomatonEdge,
      (edge ∈ parent.edges ∧ edge.source = childState index state) ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧ edge = childPendingEdge index childEdge) :
    (⟨parent.states, parent.edges⟩ : PendingAutomaton).offersAt
        (childState index state) =
      (⟨child.states, child.edges⟩ : PendingAutomaton).offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hAction⟩
    obtain ⟨childEdge, hChildEdge, hChildSource, rfl⟩ :=
      (hOutgoing edge).mp ⟨hEdge, hSource⟩
    by_cases hTock : childEdge.label.semantic = TypeLabel.tock
    · rw [if_pos (by simpa [childPendingEdge] using hTock)] at hAction
      simp at hAction
    · refine ⟨childEdge, ⟨hChildEdge, hChildSource⟩, ?_⟩
      rw [if_neg hTock]
      rw [if_neg (by simpa [childPendingEdge] using hTock)] at hAction
      cases hFuture : childEdge.future with
      | explicit offers =>
          simpa [childPendingEdge, childFutureSpec, hFuture] using hAction
      | «at» target removed =>
          simpa [childPendingEdge, childFutureSpec, hFuture] using hAction
  · rintro ⟨childEdge, ⟨hChildEdge, hChildSource⟩, hAction⟩
    obtain ⟨hEdge, hSource⟩ :=
      (hOutgoing (childPendingEdge index childEdge)).mpr
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge index childEdge, ⟨hEdge, hSource⟩, ?_⟩
    by_cases hTock : childEdge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hAction
      simp at hAction
    · rw [if_neg hTock] at hAction
      rw [if_neg (by simpa [childPendingEdge] using hTock)]
      cases hFuture : childEdge.future with
      | explicit offers =>
          simpa [childPendingEdge, childFutureSpec, hFuture] using hAction
      | «at» target removed =>
          simpa [childPendingEdge, childFutureSpec, hFuture] using hAction

theorem computeFutureOfFuel_child_embedding

    (parentType childType : PactType)
    (parentFuel childFuel : Nat)
    (parentFragment childFragment : AutomatonFragment)
    (index : Nat)
    (hParentCompile :
      compileTypeFuel parentFuel parentType = parentFragment)
    (hChildCompile :
      compileTypeFuel childFuel childType = childFragment)
    (hParentFuel : TypeCompilationFuelSufficient parentType parentFuel)
    (hChildFuel : TypeCompilationFuelSufficient childType childFuel)
    (hChildDisjoint : childType.OfferBranchesDisjoint)
    (hChildAlphabet : childType.alphabet = parentType.alphabet)
    (hChildFits : childFuel + 1 ≤ parentFuel)
    (hProductInfo : ∀ visited,
      stateProductInfo parentType (childState index visited) =
        stateProductInfo childType visited)
    (hOutgoing : ∀ (q : TypeAutomatonState) (edge : PendingAutomatonEdge),
      (edge ∈ parentFragment.edges ∧ edge.source = childState index q) ↔
        ∃ childEdge ∈ childFragment.edges,
          childEdge.source = q ∧ edge = childPendingEdge index childEdge)
    (hCard : childFragment.states.card ≤ parentFragment.states.card)
    (state : TypeAutomatonState)
    (hState : state ∈ childFragment.states)
    (hMenuReferences : ∀ source,
      menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel parentType) parentType)
        (childState index source) =
      (menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel childType) childType) source).image
        (childState index) := by
      intro source
      first
      | apply menuDependencyTargets_choice_left
      | apply menuDependencyTargets_choice_right
      | apply menuDependencyTargets_fairChoice_left
      | apply menuDependencyTargets_fairChoice_right
      | apply menuDependencyTargets_xoffer_else
      | apply menuDependencyTargets_xoffer_branch
      | apply menuDependencyTargets_offer_else
      | apply menuDependencyTargets_offer_branch
      all_goals assumption) :
    computeFutureOfFuel parentFuel parentType
        (childState index state) =
      computeFutureOfFuel childFuel childType state := by
  classical
  obtain ⟨parentRest, hParentEq⟩ :
      ∃ rest, parentFuel = rest + 1 := by
    have hPositive := TypeCompilationFuelSufficient.positive hParentFuel
    exact ⟨parentFuel - 1, by omega⟩
  obtain ⟨childRest, hChildEq⟩ :
      ∃ rest, childFuel = rest + 1 := by
    have hPositive := TypeCompilationFuelSufficient.positive hChildFuel
    exact ⟨childFuel - 1, by omega⟩
  subst parentFuel
  subst childFuel
  let parent : PendingAutomaton :=
    { states := parentFragment.states, edges := parentFragment.edges }
  let child : PendingAutomaton :=
    { states := childFragment.states, edges := childFragment.edges }
  let parentMenu := parent.withMenuDependencies
    (compileTypeMenuLinksFuel (typeCompilationFuel parentType) parentType)
  let childMenu := child.withMenuDependencies
    (compileTypeMenuLinksFuel (typeCompilationFuel childType) childType)
  have hReachable :
      parentMenu.futureReachable (childState index state) =
        (childMenu.futureReachable state).image (childState index) := by
    apply FiniteMenuGraph.futureReachable_eq_of_embedding childMenu parentMenu
      (childState index)
    · intro visited
      change parent.referencedStates (childState index visited) ∪
        menuDependencyTargets _ (childState index visited) =
          (child.referencedStates visited ∪ menuDependencyTargets _ visited).image (childState index)
      rw [referencedStates_of_outgoing_childPendingEdge
        parentFragment childFragment index visited (hOutgoing visited),
        hMenuReferences visited, Finset.image_union]
    · simpa only [childMenu, child, compiledMenuGraphFuel, hChildCompile,
        Nat.min_eq_right hChildFuel] using
        compiledMenuGraphFuel_referencesClosed (childRest + 1) childType hChildFuel hChildDisjoint
    · simpa [child] using hState
    · exact hCard
  conv_lhs => rw [computeFutureOfFuel]
  conv_rhs => rw [computeFutureOfFuel]
  rw [hParentCompile, hChildCompile]
  simp only [Nat.min_eq_right hParentFuel, Nat.min_eq_right hChildFuel]
  rw [hChildAlphabet]
  refine congrArg (Finset.filter _) ?_
  change (parentMenu.futureReachable (childState index state)).biUnion
      (_ : TypeAutomatonState → Finset BareMessage) =
    (childMenu.futureReachable state).biUnion
      (_ : TypeAutomatonState → Finset BareMessage)
  rw [hReachable, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro visited _hVisited
  have hOffers := offersAt_of_outgoing_childPendingEdge
    parentFragment childFragment index visited (hOutgoing visited)
  change parent.offersAt (childState index visited) =
    child.offersAt visited at hOffers
  rw [hOffers, hProductInfo visited]
  cases hProduct : stateProductInfo childType visited with
  | none => rfl
  | some info =>
      rcases info with ⟨interface, productLeft, productRight, q1, q2⟩
      have hProductFuel :
          stateProductInfoFuel (typeCompilationFuel childType) childType visited =
            some (interface, productLeft, productRight, q1, q2) := by
        simpa [stateProductInfo] using hProduct
      obtain ⟨hLeftLt, hRightLt⟩ :=
        stateProductInfoFuel_component_fuel_lt
          (typeCompilationFuel childType) childType visited interface
          productLeft productRight q1 q2
          (typeCompilationFuel_sufficient childType) hProductFuel
      have hLeftSmall :
          TypeCompilationFuelSufficient productLeft childRest := by
        simp [TypeCompilationFuelSufficient] at hLeftLt hChildFuel ⊢
        omega
      have hRightSmall :
          TypeCompilationFuelSufficient productRight childRest := by
        simp [TypeCompilationFuelSufficient] at hRightLt hChildFuel ⊢
        omega
      have hLeftLarge :
          TypeCompilationFuelSufficient productLeft parentRest := by
        simp [TypeCompilationFuelSufficient] at hChildFits hLeftSmall ⊢
        omega
      have hRightLarge :
          TypeCompilationFuelSufficient productRight parentRest := by
        simp [TypeCompilationFuelSufficient] at hChildFits hRightSmall ⊢
        omega
      simp only
      rw [computeFutureOfFuel_eq_of_sufficient productLeft q1
          hLeftLarge hLeftSmall,
        computeFutureOfFuel_eq_of_sufficient productRight q2
          hRightLarge hRightSmall]

private theorem buildExclusiveOfferAutomaton_outgoing_else
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton alphabet branches
      elseAutomaton branchAutomata
    edge ∈ offer.edges ∧ edge.source = .child 0 state ↔
      ∃ childEdge ∈ elseAutomaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, hChildEdge, hEdgeEq⟩
      have hChildSource := hSource
      rw [← hEdgeEq] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdgeEq.symm⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, _hIndexed, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, _hChildEdge, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl (Or.inl
        ⟨childEdge, hChildEdge, rfl⟩)))
    · simp [childPendingEdge, childState, hChildSource]

private theorem buildExclusiveOfferAutomaton_outgoing_branch
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : branchAutomata[i]? = some (action, automaton))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton alphabet branches
      elseAutomaton branchAutomata
    edge ∈ offer.edges ∧ edge.source = .child (i + 1) state ↔
      ∃ childEdge ∈ automaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge (i + 1) childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranchEdges) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, _hChildEdge, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEdgeEq⟩
        have hChildSource := hSource
        rw [← hEdgeEq] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        rcases hChildSource with ⟨hIndexEq, hSourceEq⟩
        have hIndexedGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        have hEntryEq : indexed.1 = (action, automaton) := by
          have hGet : branchAutomata[i]? = some indexed.1 := by
            simpa [hIndexEq] using hIndexedGet
          rw [hBranch] at hGet
          exact (Option.some.inj hGet).symm
        have hAutomatonEq : indexed.1.2 = automaton :=
          congrArg Prod.snd hEntryEq
        have hEdgeEq' : edge = childPendingEdge (i + 1) childEdge := by
          simpa [hIndexEq] using hEdgeEq.symm
        exact ⟨childEdge, by simpa [hAutomatonEq] using hChildEdge,
          hSourceEq, hEdgeEq'⟩
    · rw [mem_foldl_union_iff] at hBranchEdges
      rcases hBranchEdges with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      rw [indexedFragmentEdges, mem_foldl_union_iff]
      exact Or.inr ⟨((action, automaton), i),
        List.mk_mem_zipIdx_iff_getElem?.mpr hBranch,
        Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩⟩
    · simp [childPendingEdge, childState, hChildSource]

/-- Proves a `.child 0`-tagged state's future menu, in a compiled binary choice, agrees with the left child's own. -/
theorem computeFutureOf_binaryChoice_left
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (whole : PactType)
    (hWhole :
      compileTypeFuel (typeCompilationFuel whole) whole =
        buildChoiceAutomaton alphabet
          (compileTypeFuel (typeCompilationFuel left) left)
          (compileTypeFuel (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole)
    (hDisjoint : left.OfferBranchesDisjoint)
    (hChildAlphabet : left.alphabet = whole.alphabet)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child 0 visited) =
        stateProductInfo left visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel (typeCompilationFuel left)
      left).states)
    (hMenuReferences : ∀ source,
      menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel whole) whole)
        (.child 0 source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel left) left)
        source).image (.child 0) := by
      intro source
      first
      | apply menuDependencyTargets_choice_left
      | apply menuDependencyTargets_fairChoice_left) :
    computeFutureOf whole (.child 0 state) =
      computeFutureOf left state := by
  classical
  let leftFragment :=
    compileTypeFuel (typeCompilationFuel left) left
  let rightFragment :=
    compileTypeFuel (typeCompilationFuel right) right
  let parentFragment :=
    buildChoiceAutomaton alphabet leftFragment rightFragment
      selectionLeft selectionRight
  have hCard : leftFragment.states.card ≤ parentFragment.states.card := by
    have hTaggedCard :
        (childStates 0 leftFragment).card = leftFragment.states.card := by
      unfold childStates
      apply Finset.card_image_of_injective
      intro first second hEq
      simpa [childState] using hEq
    change leftFragment.states.card ≤ parentFragment.states.card
    rw [← hTaggedCard]
    apply Finset.card_le_card
    intro tagged hTagged
    simp only [parentFragment, buildChoiceAutomaton, finishAutomatonFragment,
      Finset.mem_union]
    exact Or.inl (Or.inr hTagged)
  unfold computeFutureOf
  exact computeFutureOfFuel_child_embedding whole left
    (typeCompilationFuel whole) (typeCompilationFuel left)
    parentFragment leftFragment 0 hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient left) hDisjoint hChildAlphabet hFuel
    hProductInfo
    (fun q edge => buildChoiceAutomaton_outgoing_left alphabet
      leftFragment rightFragment selectionLeft selectionRight q edge)
    hCard state (by simpa [leftFragment] using hState) hMenuReferences

/-- Proves a `.child 1`-tagged state's future menu, in a compiled binary choice, agrees with the right child's own. -/
theorem computeFutureOf_binaryChoice_right
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (whole : PactType)
    (hWhole :
      compileTypeFuel (typeCompilationFuel whole) whole =
        buildChoiceAutomaton alphabet
          (compileTypeFuel (typeCompilationFuel left) left)
          (compileTypeFuel (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel right + 1 ≤ typeCompilationFuel whole)
    (hDisjoint : right.OfferBranchesDisjoint)
    (hChildAlphabet : right.alphabet = whole.alphabet)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child 1 visited) =
        stateProductInfo right visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel (typeCompilationFuel right)
      right).states)
    (hMenuReferences : ∀ source,
      menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel whole) whole)
        (.child 1 source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel right) right)
        source).image (.child 1) := by
      intro source
      first
      | apply menuDependencyTargets_choice_right
      | apply menuDependencyTargets_fairChoice_right) :
    computeFutureOf whole (.child 1 state) =
      computeFutureOf right state := by
  classical
  let leftFragment :=
    compileTypeFuel (typeCompilationFuel left) left
  let rightFragment :=
    compileTypeFuel (typeCompilationFuel right) right
  let parentFragment :=
    buildChoiceAutomaton alphabet leftFragment rightFragment
      selectionLeft selectionRight
  have hCard : rightFragment.states.card ≤ parentFragment.states.card := by
    have hTaggedCard :
        (childStates 1 rightFragment).card = rightFragment.states.card := by
      unfold childStates
      apply Finset.card_image_of_injective
      intro first second hEq
      simpa [childState] using hEq
    change rightFragment.states.card ≤ parentFragment.states.card
    rw [← hTaggedCard]
    apply Finset.card_le_card
    intro tagged hTagged
    simp only [parentFragment, buildChoiceAutomaton, finishAutomatonFragment,
      Finset.mem_union]
    exact Or.inr hTagged
  unfold computeFutureOf
  exact computeFutureOfFuel_child_embedding whole right
    (typeCompilationFuel whole) (typeCompilationFuel right)
    parentFragment rightFragment 1 hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient right) hDisjoint hChildAlphabet hFuel
    hProductInfo
    (fun q edge => buildChoiceAutomaton_outgoing_right alphabet
      leftFragment rightFragment selectionLeft selectionRight q edge)
    hCard state (by simpa [rightFragment] using hState) hMenuReferences

/-- Proves a `.child 0`-tagged state's future menu, in a compiled exclusive offer, agrees with the else child's own. -/
theorem computeFutureOf_exclusiveOffer_else
     {alphabet : PactTypeAlphabet}
    (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel (typeCompilationFuel whole) whole =
        buildExclusiveOfferAutomaton alphabet branches
          (compileTypeFuel (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel
            (typeCompilationFuel branch.2) branch.2)))
    (hFuel : typeCompilationFuel elseType + 1 ≤ typeCompilationFuel whole)
    (hDisjoint : elseType.OfferBranchesDisjoint)
    (hChildAlphabet : elseType.alphabet = whole.alphabet)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child 0 visited) =
        stateProductInfo elseType visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel (typeCompilationFuel elseType)
      elseType).states)
    (hMenuReferences : ∀ source,
      menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel whole) whole)
        (.child 0 source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel elseType) elseType)
        source).image (.child 0) := by
      intro source
      apply menuDependencyTargets_xoffer_else) :
    computeFutureOf whole (.child 0 state) =
      computeFutureOf elseType state := by
  classical
  let elseFragment :=
    compileTypeFuel (typeCompilationFuel elseType) elseType
  let branchFragments := branches.map fun branch =>
    (branch.1, compileTypeFuel (typeCompilationFuel branch.2)
      branch.2)
  let parentFragment :=
    buildExclusiveOfferAutomaton alphabet branches elseFragment
      branchFragments
  have hCard : elseFragment.states.card ≤ parentFragment.states.card := by
    have hTaggedCard :
        (childStates 0 elseFragment).card = elseFragment.states.card := by
      unfold childStates
      apply Finset.card_image_of_injective
      intro first second hEq
      simpa [childState] using hEq
    change elseFragment.states.card ≤ parentFragment.states.card
    rw [← hTaggedCard]
    apply Finset.card_le_card
    intro tagged hTagged
    simp only [parentFragment, buildExclusiveOfferAutomaton,
      finishAutomatonFragment, Finset.mem_union]
    exact Or.inl (Or.inr hTagged)
  unfold computeFutureOf
  exact computeFutureOfFuel_child_embedding whole elseType
    (typeCompilationFuel whole) (typeCompilationFuel elseType)
    parentFragment elseFragment 0 hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient elseType) hDisjoint hChildAlphabet hFuel
    hProductInfo
    (fun q edge => buildExclusiveOfferAutomaton_outgoing_else alphabet
      branches elseFragment branchFragments q edge)
    hCard state (by simpa [elseFragment] using hState) hMenuReferences

/-- Proves a `.child (i+1)`-tagged state's future menu, in a compiled exclusive offer, agrees with branch `i`'s own. -/
theorem computeFutureOf_exclusiveOffer_branch
     {alphabet : PactTypeAlphabet}
    (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel (typeCompilationFuel whole) whole =
        buildExclusiveOfferAutomaton alphabet branches
          (compileTypeFuel (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel
            (typeCompilationFuel branch.2) branch.2)))
    (i : Nat) (action : BareMessage) (branchType : PactType)
    (hBranch : branches[i]? = some (action, branchType))
    (hFuel : typeCompilationFuel branchType + 1 ≤ typeCompilationFuel whole)
    (hDisjoint : branchType.OfferBranchesDisjoint)
    (hChildAlphabet : branchType.alphabet = whole.alphabet)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child (i + 1) visited) =
        stateProductInfo branchType visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel (typeCompilationFuel branchType)
      branchType).states)
    (hMenuReferences : ∀ source,
      menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel whole) whole)
        (.child (i + 1) source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel branchType) branchType)
        source).image (.child (i + 1)) := by
      intro source
      apply menuDependencyTargets_xoffer_branch
      assumption) :
    computeFutureOf whole (.child (i + 1) state) =
      computeFutureOf branchType state := by
  classical
  let elseFragment :=
    compileTypeFuel (typeCompilationFuel elseType) elseType
  let branchFragments := branches.map fun branch =>
    (branch.1, compileTypeFuel (typeCompilationFuel branch.2)
      branch.2)
  let branchFragment :=
    compileTypeFuel (typeCompilationFuel branchType) branchType
  let parentFragment :=
    buildExclusiveOfferAutomaton alphabet branches elseFragment
      branchFragments
  have hBranchFragment :
      branchFragments[i]? = some (action, branchFragment) := by
    simp [branchFragments, branchFragment, List.getElem?_map, hBranch]
  have hCard : branchFragment.states.card ≤ parentFragment.states.card := by
    have hTaggedCard :
        (childStates (i + 1) branchFragment).card =
          branchFragment.states.card := by
      unfold childStates
      apply Finset.card_image_of_injective
      intro first second hEq
      simpa [childState] using hEq
    change branchFragment.states.card ≤ parentFragment.states.card
    rw [← hTaggedCard]
    apply Finset.card_le_card
    intro tagged hTagged
    have hIndexed : tagged ∈ indexedFragmentStates branchFragments := by
      rw [indexedFragmentStates, mem_foldl_union_iff]
      exact Or.inr ⟨((action, branchFragment), i),
        List.mk_mem_zipIdx_iff_getElem?.mpr hBranchFragment, hTagged⟩
    simp only [parentFragment, buildExclusiveOfferAutomaton,
      finishAutomatonFragment, Finset.mem_union]
    exact Or.inr hIndexed
  unfold computeFutureOf
  exact computeFutureOfFuel_child_embedding whole branchType
    (typeCompilationFuel whole) (typeCompilationFuel branchType)
    parentFragment branchFragment (i + 1) hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient branchType) hDisjoint hChildAlphabet hFuel
    hProductInfo
    (fun q edge => buildExclusiveOfferAutomaton_outgoing_branch alphabet
      branches elseFragment branchFragments i action branchFragment
      hBranchFragment q edge)
    hCard state (by simpa [branchFragment] using hState) hMenuReferences


/-- A compiled fragment references only states it declares: every symbolic
future field points at a declared state. -/
theorem referencesClosed_compileTypeFuel (processType : PactType) (fuel : Nat)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hDisjoint : processType.OfferBranchesDisjoint) :
    PendingAutomaton.ReferencesClosed
      { states := (compileTypeFuel fuel processType).states,
        edges := (compileTypeFuel fuel processType).edges } := by
  classical
  have hTargets :=
    compileTypeFuel_futureTargetsInStates fuel processType hFuel hDisjoint
  intro state _ reference hReference
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hReference
  obtain ⟨edge, ⟨hEdge, -⟩, hIn⟩ := hReference
  by_cases hTock : edge.label.semantic = TypeLabel.tock
  · rw [if_pos hTock] at hIn
    exact absurd hIn (Finset.notMem_empty _)
  · rw [if_neg hTock] at hIn
    cases hFuture : edge.future with
    | explicit offers =>
        rw [hFuture] at hIn
        exact absurd hIn (Finset.notMem_empty _)
    | «at» target removed =>
        rw [hFuture, Finset.mem_singleton] at hIn
        rw [hIn]
        exact hTargets edge hEdge target removed hFuture

/-- A binary-choice root carries no product term of its own. -/
theorem stateProductInfo_choice_root (alphabet : PactTypeAlphabet)
    (left right : PactType) :
    stateProductInfo (.choice alphabet left right) TypeAutomatonState.root =
      none := by
  obtain ⟨k, hk⟩ : ∃ k, typeCompilationFuel (.choice alphabet left right) =
      k + 1 :=
    ⟨typeCompilationFuel (.choice alphabet left right) - 1, by
      have := typeCompilationFuel_positive (.choice alphabet left right)
      omega⟩
  simp only [stateProductInfo, hk, stateProductInfoFuel]

/-- A child tag peels off a binary choice's product information. -/
theorem stateProductInfo_choice_child_left (alphabet : PactTypeAlphabet)
    (left right : PactType) (q : TypeAutomatonState) :
    stateProductInfo (.choice alphabet left right) (.child 0 q) =
      stateProductInfo left q := by
  have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel]
  exact stateProductInfoFuel_eq_of_sufficient left q
    (Nat.le_max_left _ _) (Nat.le_refl _)

/-- Mirror for the right child. -/
theorem stateProductInfo_choice_child_right (alphabet : PactTypeAlphabet)
    (left right : PactType) (q : TypeAutomatonState) :
    stateProductInfo (.choice alphabet left right) (.child 1 q) =
      stateProductInfo right q := by
  have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel]
  exact stateProductInfoFuel_eq_of_sufficient right q
    (Nat.le_max_right _ _) (Nat.le_refl _)

/-- A fair-choice root carries no product term of its own. -/
theorem stateProductInfo_fairChoice_root (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType) :
    stateProductInfo (.fairChoice alphabet bid left right)
        TypeAutomatonState.root = none := by
  obtain ⟨k, hk⟩ : ∃ k,
      typeCompilationFuel (.fairChoice alphabet bid left right) = k + 1 :=
    ⟨typeCompilationFuel (.fairChoice alphabet bid left right) - 1, by
      have := typeCompilationFuel_positive
        (.fairChoice alphabet bid left right)
      omega⟩
  simp only [stateProductInfo, hk, stateProductInfoFuel]

/-- A child tag peels off a fair choice's product information. -/
theorem stateProductInfo_fairChoice_child_left (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType) (q : TypeAutomatonState) :
    stateProductInfo (.fairChoice alphabet bid left right) (.child 0 q) =
      stateProductInfo left q := by
  have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel]
  exact stateProductInfoFuel_eq_of_sufficient left q
    (Nat.le_max_left _ _) (Nat.le_refl _)

/-- Mirror for the right child. -/
theorem stateProductInfo_fairChoice_child_right (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType) (q : TypeAutomatonState) :
    stateProductInfo (.fairChoice alphabet bid left right) (.child 1 q) =
      stateProductInfo right q := by
  have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel]
  exact stateProductInfoFuel_eq_of_sufficient right q
    (Nat.le_max_right _ _) (Nat.le_refl _)

/-- An exclusive-offer root carries no product term of its own. -/
theorem stateProductInfo_xoffer_root (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    stateProductInfo (.xoffer alphabet elseType branches)
        TypeAutomatonState.root = none := by
  obtain ⟨k, hk⟩ : ∃ k,
      typeCompilationFuel (.xoffer alphabet elseType branches) = k + 1 :=
    ⟨typeCompilationFuel (.xoffer alphabet elseType branches) - 1, by
      have := typeCompilationFuel_positive (.xoffer alphabet elseType branches)
      omega⟩
  simp only [stateProductInfo, hk, stateProductInfoFuel]

/-- The default tag peels off an exclusive offer's product information. -/
theorem stateProductInfo_xoffer_child_else (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (q : TypeAutomatonState) :
    stateProductInfo (.xoffer alphabet elseType branches) (.child 0 q) =
      stateProductInfo elseType q := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType)
        (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel]
  exact stateProductInfoFuel_eq_of_sufficient elseType q
    (Nat.le_max_left _ _) (Nat.le_refl _)

/-- So does a branch tag. -/
theorem stateProductInfo_xoffer_child_branch (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (action : BareMessage) (branchType : PactType)
    (hBranch : branches[i]? = some (action, branchType))
    (q : TypeAutomatonState) :
    stateProductInfo (.xoffer alphabet elseType branches) (.child (i + 1) q) =
      stateProductInfo branchType q := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType)
        (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hFuel : typeCompilationFuel branchType ≤
      max (typeCompilationFuel elseType)
        (typeBranchCompilationFuel branches) := by
    have hLe := typeCompilationFuel_le_typeBranchCompilationFuel branches
      (action, branchType) (List.mem_of_getElem? hBranch)
    simp only at hLe
    omega
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel, hBranch]
  exact stateProductInfoFuel_eq_of_sufficient branchType q hFuel
    (Nat.le_refl _)

/-- A root's menu splits into its own offers and the menus of the states it
references.  This is the menu equation at every non-parallel root: the root
reaches exactly its copied child entries, and contributes no product term of
its own.  States below it may still be product states. -/
theorem computeFutureOf_root_decomposition (whole : PactType)
    (source : TypeAutomatonState) (entries : Finset TypeAutomatonState)
    (pending : PendingAutomaton)
    (hPending : pending =
      { states := (compileTypeFuel (typeCompilationFuel whole) whole).states,
        edges := (compileTypeFuel (typeCompilationFuel whole) whole).edges })
    (hClosed : pending.ReferencesClosed)
    (hSource : source ∈ pending.states)
    (hUpper : pending.referencedStates source ⊆ insert source entries)
    (hEntries : entries ⊆ pending.referencedStates source)
    (hNoProduct : stateProductInfo whole source = none)
    (hOffersDeclared : ∀ action ∈ pending.offersAt source,
      action ∈ whole.alphabet.actions)
    (hWholeDisjoint : whole.OfferBranchesDisjoint := by assumption)
    (hRoot : source = .root := by rfl) :
    computeFutureOf whole source =
      pending.offersAt source ∪ entries.biUnion (computeFutureOf whole) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, typeCompilationFuel whole = k + 1 :=
    ⟨typeCompilationFuel whole - 1, by
      have := typeCompilationFuel_positive whole
      omega⟩
  rw [hk] at hPending
  let graph := pending.withMenuDependencies
    (compileTypeMenuLinksFuel (typeCompilationFuel whole) whole)
  have hGraphClosed : graph.ReferencesClosed := by
    simpa only [graph, hPending, compiledMenuGraphFuel, hk, Nat.min_self] using
      compiledMenuGraphFuel_referencesClosed (typeCompilationFuel whole) whole le_rfl hWholeDisjoint
  have hGraphReferences : graph.referencedStates source = pending.referencedStates source := by
    change pending.referencedStates source ∪ menuDependencyTargets
      (compileTypeMenuLinksFuel (typeCompilationFuel whole) whole) source = _
    rw [hRoot, compileTypeMenuLinksFuel_root, Finset.union_empty]
  set summand : TypeAutomatonState → Finset BareMessage := fun visited =>
    pending.offersAt visited ∪
      match stateProductInfo whole visited with
      | some (interface, left, right, q1, q2) =>
          hideTypeOffers interface
            (computeFutureOfFuel k left q1 ∪ computeFutureOfFuel k right q2)
      | none => ∅ with hSummand
  have hUnfold : ∀ state,
      computeFutureOf whole state =
        ((graph.futureReachable state).biUnion summand).filter
          fun action => action ∈ whole.alphabet.actions := by
    intro state
    unfold computeFutureOf
    rw [hk, computeFutureOfFuel]
    simp only [graph, hSummand, hPending, hk, Nat.min_self]
    rfl
  have hSourceSummand : summand source = pending.offersAt source := by
    simp only [hSummand, hNoProduct]
    simp
  have hReach := graph.futureReachable_eq_self_union_biUnion source entries
    hGraphClosed hSource (by rw [hGraphReferences]; exact hUpper)
    (by rw [hGraphReferences]; exact hEntries)
  rw [hUnfold source, hReach]
  apply Finset.Subset.antisymm
  · intro action hAction
    rw [Finset.mem_filter] at hAction
    obtain ⟨hAction, hDecl⟩ := hAction
    rw [Finset.mem_biUnion] at hAction
    obtain ⟨visited, hVisited, hIn⟩ := hAction
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
      at hVisited ⊢
    rcases hVisited with rfl | ⟨entry, hEntry, hEntryReach⟩
    · rw [hSourceSummand] at hIn
      exact Or.inl hIn
    · refine Or.inr ⟨entry, hEntry, ?_⟩
      rw [hUnfold entry, Finset.mem_filter, Finset.mem_biUnion]
      exact ⟨⟨visited, hEntryReach, hIn⟩, hDecl⟩
  · intro action hAction
    simp only [Finset.mem_union, Finset.mem_biUnion] at hAction
    rw [Finset.mem_filter, Finset.mem_biUnion]
    rcases hAction with hIn | ⟨entry, hEntry, hIn⟩
    · refine ⟨⟨source, by simp, ?_⟩, ?_⟩
      · rw [hSourceSummand]; exact hIn
      · exact hOffersDeclared action hIn
    · rw [hUnfold entry, Finset.mem_filter, Finset.mem_biUnion] at hIn
      obtain ⟨⟨visited, hVisited, hInner⟩, hDecl⟩ := hIn
      refine ⟨⟨visited, ?_, hInner⟩, hDecl⟩
      simp only [Finset.mem_union, Finset.mem_biUnion]
      exact Or.inr ⟨entry, hEntry, hVisited⟩


end

end Pact
