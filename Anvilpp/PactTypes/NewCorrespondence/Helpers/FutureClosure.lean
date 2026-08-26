import Anvilpp.PactTypes.NewCorrespondence.Helpers.EnvironmentAndAlphabet

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
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftTargets : left.EdgeTargetsInStates)
    (hRightTargets : right.EdgeTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    (buildChoiceAutomaton signature left right selectionLeft
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
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hBodyTargets : body.EdgeTargetsInStates)
    (hBodyInitial : body.initial ∈ body.states) :
    (buildRecursionAutomaton signature name body).EdgeTargetsInStates := by
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
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (hLeftTargets : left.EdgeTargetsInStates)
    (hRightTargets : right.EdgeTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    (buildSequenceAutomaton signature left right).EdgeTargetsInStates := by
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
        not_mem_sequenceDeleted_of_not_accepting hNotAccepting⟩, rfl⟩
  · obtain ⟨rightEdge, hRightEdge, rfl⟩ := hRight
    simp [childPendingEdge, buildSequenceAutomaton,
      finishAutomatonFragment, childStates, childState,
      hRightTargets rightEdge hRightEdge]
  · obtain ⟨leftEdge, _, rfl⟩ := hRedirect
    simp [sequenceRedirectEdge, buildSequenceAutomaton,
      finishAutomatonFragment, childStates, childState, hRightInitial]

private theorem buildParallelAutomaton_edgeTargetsInStates
    (signature : TypeAlphabet)
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage)
    (hLeftTargets : left.EdgeTargetsInStates)
    (hRightTargets : right.EdgeTargetsInStates) :
    (buildParallelAutomaton signature parentAlphabet leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture).EdgeTargetsInStates := by
  intro edge hEdge
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    parallelRawTransitionEdges, parallelDoneEdges,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with
      ⟨⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, _⟩, rfl⟩, _⟩ |
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
  · simp [buildParallelAutomaton, finishAutomatonFragment,
      parallelRawTransitionEdges, parallelDoneEdges]

private theorem buildExclusiveOfferAutomaton_edgeTargetsInStates
    (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.EdgeTargetsInStates)
    (hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.EdgeTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states) :
    (buildExclusiveOfferAutomaton signature branches elseAutomaton
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
    (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.EdgeTargetsInStates)
    (hConjunctionTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.EdgeTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states) :
    (buildSelectedConjunctiveOfferAutomaton signature branches elseAutomaton
      selectedConjunctions).EdgeTargetsInStates := by
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
theorem compileTypeFuel_edgeTargetsInStates (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      (compileTypeFuel signature fuel processType).EdgeTargetsInStates := by
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
          rw [compileTypeFuel.eq_def]
          exact buildRecursionAutomaton_edgeTargetsInStates signature name
            (compileTypeFuel signature fuel body) (ih body hBody)
            (compileTypeFuel_initial_mem signature fuel body hBody)
      | choice _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_edgeTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) .silent .silent
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | fairChoice _ bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_edgeTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) (.fair bid true)
            (.fair bid false) (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | seq _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildSequenceAutomaton_edgeTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) (ih left hLeft)
            (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | par alphabet left right interface =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildParallelAutomaton_edgeTargetsInStates signature alphabet
            left.alphabet right.alphabet interface
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (compiledChildFutureFuel signature fuel left)
            (compiledChildFutureFuel signature fuel right)
            (ih left hLeft) (ih right hRight)
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
          apply buildExclusiveOfferAutomaton_edgeTargetsInStates
          · exact ih elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact ih original.2 (hBranches original hOriginal)
          · exact compileTypeFuel_initial_mem signature fuel elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact compileTypeFuel_initial_mem signature fuel original.2
              (hBranches original hOriginal)
      | offer _ elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hSelected : ∀ selected ∈ branches,
              TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting selected branches) fuel := by
            intro selected hSelected
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          rw [compileTypeFuel.eq_def]
          apply buildSelectedConjunctiveOfferAutomaton_edgeTargetsInStates
          · exact ih elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact ih (parallelTypeBranchesSelecting original branches)
              (hSelected original hOriginal)
          · exact compileTypeFuel_initial_mem signature fuel elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            obtain ⟨original, hOriginal, rfl⟩ := hEntry
            exact compileTypeFuel_initial_mem signature fuel
              (parallelTypeBranchesSelecting original branches)
              (hSelected original hOriginal)

theorem compileTypeFuel_futureTargetsInStates (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      (compileTypeFuel signature fuel processType).FutureTargetsInStates := by
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
            simp at hFuture
          rcases hFuture with ⟨rfl, rfl⟩
          simp [compileTypeFuel, finishAutomatonFragment]
      | tock _ =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩
          · split at hFuture <;> simp at hFuture
          · simp at hFuture
      | skip _ =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image]
            at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp at hFuture
      | var _ name =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image]
            at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp at hFuture
      | recur _ name body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildRecursionAutomaton_futureTargetsInStates signature name
            (compileTypeFuel signature fuel body) (ih body hBody)
            (compileTypeFuel_initial_mem signature fuel body hBody)
      | choice _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) TypeLabel.silent
            TypeLabel.silent (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | fairChoice _ bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | seq _ left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildSequenceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) (ih right hRight)
            (compileTypeFuel_edgeTargetsInStates signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | par alphabet left right interface =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          rw [compileTypeFuel.eq_def]
          exact buildParallelAutomaton_futureTargetsInStates signature alphabet
            left.alphabet right.alphabet interface
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (compiledChildFutureFuel signature fuel left)
            (compiledChildFutureFuel signature fuel right)
            (compileTypeFuel_edgeTargetsInStates signature fuel left hLeft)
            (compileTypeFuel_edgeTargetsInStates signature fuel right hRight)
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
          have hResult := buildExclusiveOfferAutomaton_futureTargetsInStates
            signature branches (compileTypeFuel signature fuel elseType)
            (branches.map fun branch =>
              (branch.1, compileTypeFuel signature fuel branch.2))
            (ih elseType hElse)
            (by
              intro entry hEntry
              simp only [List.mem_map] at hEntry
              obtain ⟨original, hOriginal, rfl⟩ := hEntry
              exact ih original.2 (hBranches original hOriginal))
            (compileTypeFuel_initial_mem signature fuel elseType hElse)
            (by
              intro entry hEntry
              simp only [List.mem_map] at hEntry
              obtain ⟨original, hOriginal, rfl⟩ := hEntry
              exact compileTypeFuel_initial_mem signature fuel original.2
                (hBranches original hOriginal))
          simpa [compileTypeFuel] using hResult
      | offer _ elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hSelected : ∀ selected ∈ branches,
              TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting selected branches) fuel := by
            intro selected hSelected
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          rw [compileTypeFuel.eq_def]
          have hResult :=
            buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates
              signature branches (compileTypeFuel signature fuel elseType)
              (branches.map fun selected =>
                (selected.1, compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting selected branches)))
              (ih elseType hElse)
              (by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨original, hOriginal, rfl⟩ := hEntry
                exact ih (parallelTypeBranchesSelecting original branches)
                  (hSelected original hOriginal))
              (compileTypeFuel_initial_mem signature fuel elseType hElse)
              (by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨original, hOriginal, rfl⟩ := hEntry
                exact compileTypeFuel_initial_mem signature fuel
                  (parallelTypeBranchesSelecting original branches)
                  (hSelected original hOriginal))
          simpa [compileTypeFuel] using hResult

/-- Proves every sufficiently fuelled fragment's pending automaton is closed under its own future references. -/
theorem compileTypeFuel_referencesClosed (signature : TypeAlphabet)
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    ({ states := (compileTypeFuel signature fuel processType).states
       edges := (compileTypeFuel signature fuel processType).edges } :
      PendingAutomaton).ReferencesClosed :=
  PendingAutomaton.referencesClosed_of_futureTargetsInStates
    (compileTypeFuel signature fuel processType)
    (compileTypeFuel_futureTargetsInStates signature fuel processType hFuel)

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
      | par _ left right interface =>
          cases state <;> rfl
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
      | par _ left right productInterface =>
          cases state with
          | pair leftState rightState =>
              simp only [stateProductInfoFuel, Option.some.injEq,
                Prod.mk.injEq] at hInfo
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hInfo
              simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
              constructor <;> omega
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
      | offer _ elseType branches =>
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
                        ih (parallelTypeBranchesSelecting selected branches) state
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
    ∀ fuel signature processType state,
      TypeCompilationFuelSufficient processType fuel →
      computeFutureOfFuel signature (fuel + 1) processType state =
        computeFutureOfFuel signature fuel processType state := by
  intro fuel
  induction fuel with
  | zero =>
      intro signature processType state hFuel
      have hPositive := typeCompilationFuel_positive processType
      simp [TypeCompilationFuelSufficient] at hFuel
      omega
  | succ fuel ih =>
      intro signature processType state hFuel
      conv_lhs => rw [computeFutureOfFuel]
      conv_rhs => rw [computeFutureOfFuel]
      have hCompile :
          compileTypeFuel signature (fuel + 1 + 1) processType =
            compileTypeFuel signature (fuel + 1) processType :=
        compileTypeFuel_eq_of_sufficient signature processType
          (by
            simp only [TypeCompilationFuelSufficient] at hFuel ⊢
            omega)
          hFuel
      rw [hCompile]
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
          rw [ih signature left q1 hLeftFuel, ih signature right q2 hRightFuel]

private theorem computeFutureOfFuel_add_stable
    (signature : TypeAlphabet) (processType : PactType)
    (state : TypeAutomatonState) (fuel extra : Nat)
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    computeFutureOfFuel signature (fuel + extra) processType state =
      computeFutureOfFuel signature fuel processType state := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        computeFutureOfFuel_succ_stable (fuel + extra) signature processType state
          (by
            simp [TypeCompilationFuelSufficient] at hFuel ⊢
            omega),
        ih]

/-- States that `computeFutureOfFuel` stabilizes once its fuel is sufficient, mirroring `compileTypeFuel_eq_of_sufficient`. -/
theorem computeFutureOfFuel_eq_of_sufficient
    (signature : TypeAlphabet) (processType : PactType) (state : TypeAutomatonState)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    computeFutureOfFuel signature leftFuel processType state =
      computeFutureOfFuel signature rightFuel processType state := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (computeFutureOfFuel_add_stable signature processType state leftFuel
      extra hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact computeFutureOfFuel_add_stable signature processType state rightFuel
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
    (signature : TypeAlphabet)
    (parentType childType : PactType)
    (parentFuel childFuel : Nat)
    (parentFragment childFragment : AutomatonFragment)
    (index : Nat)
    (hParentCompile :
      compileTypeFuel signature parentFuel parentType = parentFragment)
    (hChildCompile :
      compileTypeFuel signature childFuel childType = childFragment)
    (hParentFuel : TypeCompilationFuelSufficient parentType parentFuel)
    (hChildFuel : TypeCompilationFuelSufficient childType childFuel)
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
    (hState : state ∈ childFragment.states) :
    computeFutureOfFuel signature parentFuel parentType
        (childState index state) =
      computeFutureOfFuel signature childFuel childType state := by
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
  have hReachable :
      parent.futureReachable (childState index state) =
        (child.futureReachable state).image (childState index) := by
    apply PendingAutomaton.futureReachable_eq_of_embedding child parent
      (childState index)
    · intro visited
      exact referencedStates_of_outgoing_childPendingEdge
        parentFragment childFragment index visited (hOutgoing visited)
    · change ({ states := childFragment.states, edges := childFragment.edges } :
        PendingAutomaton).ReferencesClosed
      rw [← hChildCompile]
      exact compileTypeFuel_referencesClosed signature (childRest + 1)
        childType hChildFuel
    · simpa [child] using hState
    · exact hCard
  conv_lhs => rw [computeFutureOfFuel]
  conv_rhs => rw [computeFutureOfFuel]
  rw [hParentCompile, hChildCompile]
  change (parent.futureReachable (childState index state)).biUnion
      (_ : TypeAutomatonState → Finset BareMessage) =
    (child.futureReachable state).biUnion
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
      rw [computeFutureOfFuel_eq_of_sufficient signature productLeft q1
          hLeftLarge hLeftSmall,
        computeFutureOfFuel_eq_of_sufficient signature productRight q2
          hRightLarge hRightSmall]

private theorem buildExclusiveOfferAutomaton_outgoing_else
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton signature branches
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
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : branchAutomata[i]? = some (action, automaton))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton signature branches
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
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child 0 visited) =
        stateProductInfo left visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel left)
      left).states) :
    computeFutureOf signature whole (.child 0 state) =
      computeFutureOf signature left state := by
  classical
  let leftFragment :=
    compileTypeFuel signature (typeCompilationFuel left) left
  let rightFragment :=
    compileTypeFuel signature (typeCompilationFuel right) right
  let parentFragment :=
    buildChoiceAutomaton signature leftFragment rightFragment
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
  exact computeFutureOfFuel_child_embedding signature whole left
    (typeCompilationFuel whole) (typeCompilationFuel left)
    parentFragment leftFragment 0 hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient left) hFuel hProductInfo
    (fun q edge => buildChoiceAutomaton_outgoing_left signature
      leftFragment rightFragment selectionLeft selectionRight q edge)
    hCard state (by simpa [leftFragment] using hState)

/-- Proves a `.child 1`-tagged state's future menu, in a compiled binary choice, agrees with the right child's own. -/
theorem computeFutureOf_binaryChoice_right
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel right + 1 ≤ typeCompilationFuel whole)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child 1 visited) =
        stateProductInfo right visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel right)
      right).states) :
    computeFutureOf signature whole (.child 1 state) =
      computeFutureOf signature right state := by
  classical
  let leftFragment :=
    compileTypeFuel signature (typeCompilationFuel left) left
  let rightFragment :=
    compileTypeFuel signature (typeCompilationFuel right) right
  let parentFragment :=
    buildChoiceAutomaton signature leftFragment rightFragment
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
  exact computeFutureOfFuel_child_embedding signature whole right
    (typeCompilationFuel whole) (typeCompilationFuel right)
    parentFragment rightFragment 1 hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient right) hFuel hProductInfo
    (fun q edge => buildChoiceAutomaton_outgoing_right signature
      leftFragment rightFragment selectionLeft selectionRight q edge)
    hCard state (by simpa [rightFragment] using hState)

/-- Proves a `.child 0`-tagged state's future menu, in a compiled exclusive offer, agrees with the else child's own. -/
theorem computeFutureOf_exclusiveOffer_else
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildExclusiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2)))
    (hFuel : typeCompilationFuel elseType + 1 ≤ typeCompilationFuel whole)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child 0 visited) =
        stateProductInfo elseType visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel elseType)
      elseType).states) :
    computeFutureOf signature whole (.child 0 state) =
      computeFutureOf signature elseType state := by
  classical
  let elseFragment :=
    compileTypeFuel signature (typeCompilationFuel elseType) elseType
  let branchFragments := branches.map fun branch =>
    (branch.1, compileTypeFuel signature (typeCompilationFuel branch.2)
      branch.2)
  let parentFragment :=
    buildExclusiveOfferAutomaton signature branches elseFragment branchFragments
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
  exact computeFutureOfFuel_child_embedding signature whole elseType
    (typeCompilationFuel whole) (typeCompilationFuel elseType)
    parentFragment elseFragment 0 hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient elseType) hFuel hProductInfo
    (fun q edge => buildExclusiveOfferAutomaton_outgoing_else signature
      branches elseFragment branchFragments q edge)
    hCard state (by simpa [elseFragment] using hState)

/-- Proves a `.child (i+1)`-tagged state's future menu, in a compiled exclusive offer, agrees with branch `i`'s own. -/
theorem computeFutureOf_exclusiveOffer_branch
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildExclusiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2)))
    (i : Nat) (action : BareMessage) (branchType : PactType)
    (hBranch : branches[i]? = some (action, branchType))
    (hFuel : typeCompilationFuel branchType + 1 ≤ typeCompilationFuel whole)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child (i + 1) visited) =
        stateProductInfo branchType visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel branchType)
      branchType).states) :
    computeFutureOf signature whole (.child (i + 1) state) =
      computeFutureOf signature branchType state := by
  classical
  let elseFragment :=
    compileTypeFuel signature (typeCompilationFuel elseType) elseType
  let branchFragments := branches.map fun branch =>
    (branch.1, compileTypeFuel signature (typeCompilationFuel branch.2)
      branch.2)
  let branchFragment :=
    compileTypeFuel signature (typeCompilationFuel branchType) branchType
  let parentFragment :=
    buildExclusiveOfferAutomaton signature branches elseFragment branchFragments
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
  exact computeFutureOfFuel_child_embedding signature whole branchType
    (typeCompilationFuel whole) (typeCompilationFuel branchType)
    parentFragment branchFragment (i + 1) hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient branchType) hFuel hProductInfo
    (fun q edge => buildExclusiveOfferAutomaton_outgoing_branch signature
      branches elseFragment branchFragments i action branchFragment
      hBranchFragment q edge)
    hCard state (by simpa [branchFragment] using hState)


end

end Pact
